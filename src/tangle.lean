import category_theory.monoidal.rigid
import category_theory.monoidal.braided

open category_theory 

namespace tangle

inductive hom : ℕ → ℕ → Type
| id (a) : hom a a
| associator_hom (a b c : ℕ) : hom ((a + b) + c) (a + (b + c))
| associator_inv (a b c : ℕ) : hom (a + (b + c)) ((a + b) + c)
| left_unitor_hom (a) : hom (0 + a) a
| left_unitor_inv (a) : hom a (0 + a)
| right_unitor_hom (a) : hom (a + 0) a
| right_unitor_inv (a) : hom a (a + 0)
| comp {a b c} (f : hom a b) (g : hom b c) : hom a c
| tensor {a b c d} (f : hom a b) (g : hom c d) : hom (a + c) (b + d)
| coevaluation (a) : hom 0 (a + a)
| evaluation (a) : hom (a + a) 0
| braiding_hom (a b) : hom (a + b) (b + a)
| braiding_inv (a b) : hom (b + a) (a + b) 
| twist_hom (a) : hom a a
| twist_inv (a) : hom a a


open hom

section

local infixr ` ⟶ᵐ `:10 := hom
local infixr ` ≫ `:80 := hom.comp -- type as \gg
local infixr ` ⊗ `:70 := hom.tensor
local notation `𝟙` := hom.id -- type as \b1
local notation `α_` := hom.associator_hom
local notation `α⁻¹_` := hom.associator_inv
local notation `ℓ_` := hom.left_unitor_hom
local notation `ℓ⁻¹_` := hom.left_unitor_inv
local notation `ρ_` := hom.right_unitor_hom
local notation `ρ⁻¹_` := hom.right_unitor_inv
local notation `η_` := hom.coevaluation
local notation `ε_` := hom.evaluation
local notation `β_` := hom.braiding_hom
local notation `β⁻¹_` := hom.braiding_inv
local notation `θ_` := hom.twist_hom
local notation `θ⁻¹_` := hom.twist_inv

inductive hom_equiv : Π {X Y : ℕ}, (X ⟶ᵐ Y) → (X ⟶ᵐ Y) → Prop
| refl {X Y} (f : X ⟶ᵐ Y) : hom_equiv f f
| symm {X Y} (f g : X ⟶ᵐ Y) : hom_equiv f g → hom_equiv g f
| trans {X Y} {f g h : X ⟶ᵐ Y} : hom_equiv f g → hom_equiv g h → hom_equiv f h
| comp {X Y Z} {f f' : X ⟶ᵐ Y} {g g' : Y ⟶ᵐ Z} :
    hom_equiv f f' → hom_equiv g g' → hom_equiv (f ≫ g) (f' ≫ g')
-- | comp_congr_left {X Y Z} (a₁ a₂ : X ⟶ᵐ Y) (b : Y ⟶ᵐ Z) :
--     hom_equiv a₁ a₂ → hom_equiv (a₁ ≫ b) (a₂ ≫ b)
-- | comp_congr_right {X Y Z} (a : X ⟶ᵐ Y) (b₁ b₂ : Y ⟶ᵐ Z) :
--     hom_equiv b₁ b₂ → hom_equiv (a ≫ b₁) (a ≫ b₂)
| tensor {W X Y Z} {f f' : W ⟶ᵐ X} {g g' : Y ⟶ᵐ Z} :
    hom_equiv f f' → hom_equiv g g' → hom_equiv (f ⊗ g) (f' ⊗ g')
| comp_id {X Y} (f : X ⟶ᵐ Y) : hom_equiv (f ≫ 𝟙 _) f
| id_comp {X Y} (f : X ⟶ᵐ Y) : hom_equiv (𝟙 _ ≫ f) f
| assoc {X Y U V} (f : X ⟶ᵐ U) (g : U ⟶ᵐ V) (h : V ⟶ᵐ Y) :
    hom_equiv ((f ≫ g) ≫ h) (f ≫ (g ≫ h))
| tensor_id {X Y} : hom_equiv ((𝟙 X) ⊗ (𝟙 Y)) (𝟙 _)
| tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂}
    (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (g₁ : Y₁ ⟶ᵐ Z₁) (g₂ : Y₂ ⟶ᵐ Z₂) :
    hom_equiv ((f₁ ≫ g₁) ⊗ (f₂ ≫ g₂)) ((f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂))
| tensor_congr_left {X₁ Y₁ X₂ Y₂} (a₁ a₂ : X₁ ⟶ᵐ Y₁) (b : X₂ ⟶ᵐ Y₂) : 
    hom_equiv a₁ a₂ → hom_equiv (a₁ ⊗ b) (a₂ ⊗ b)
| tensor_congr_right {X₁ Y₁ X₂ Y₂} (a : X₁ ⟶ᵐ Y₁) (b₁ b₂ : X₂ ⟶ᵐ Y₂) : 
    hom_equiv b₁ b₂ → hom_equiv (a ⊗ b₁) (a ⊗ b₂)
| associator_hom_inv {X Y Z} : hom_equiv (α_ X Y Z ≫ α⁻¹_ X Y Z) (𝟙 _)
| associator_inv_hom {X Y Z} : hom_equiv (α⁻¹_ X Y Z ≫ α_ X Y Z) (𝟙 _)
| associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (f₃ : X₃ ⟶ᵐ Y₃) :
    hom_equiv (((f₁ ⊗ f₂) ⊗ f₃) ≫ α_ Y₁ Y₂ Y₃)
      (α_ X₁ X₂ X₃ ≫ (f₁ ⊗ (f₂ ⊗ f₃)))
| right_unitor_hom_inv {X} : hom_equiv (ρ_ X ≫ ρ⁻¹_ X) (𝟙 _)
| right_unitor_inv_hom {X} : hom_equiv (ρ⁻¹_ X ≫ ρ_ X) (𝟙 _)
| right_unitor_naturality {X Y} (f : X ⟶ᵐ Y) : hom_equiv ((f ⊗ 𝟙 0) ≫ ρ_ Y) (ρ_ X ≫ f)
| left_unitor_hom_inv {X} : hom_equiv (ℓ_ X ≫ ℓ⁻¹_ X) (𝟙 _)
| left_unitor_inv_hom {X} : hom_equiv (ℓ⁻¹_ X ≫ ℓ_ X) (𝟙 _)
| left_unitor_naturality {X Y} (f : X ⟶ᵐ Y) : hom_equiv ((𝟙 0 ⊗ f) ≫ ℓ_ Y) (ℓ_ X ≫ f)
| pentagon {W X Y Z} : hom_equiv
    ((α_ W X Y ⊗ 𝟙 Z) ≫ α_ W (X + Y) Z ≫ (𝟙 W ⊗ α_ X Y Z))
    (α_ (W + X) Y Z ≫ α_ W X (Y + Z))
| triangle {X Y} : hom_equiv (α_ X 0 Y ≫ (𝟙 X ⊗ ℓ_ Y)) (ρ_ X ⊗ 𝟙 Y)
| coevaluation_evaluation {Y} : hom_equiv ((𝟙 Y ⊗ η_ Y) ≫ α⁻¹_ Y Y Y ≫ (ε_ Y ⊗ 𝟙 Y))
    (ρ_ Y ≫ ℓ⁻¹_ Y)
| evaluation_coevaluation {X} : hom_equiv ((η_ X ⊗ 𝟙 X) ≫ α_ X X X ≫ (𝟙 X ⊗ ε_ X))
    (ℓ_ X ≫ ρ⁻¹_ X)
| braiding_hom_inv {X Y} : hom_equiv (β_ X Y ≫ β⁻¹_ X Y) (𝟙 _)
| braiding_inv_hom {X Y} : hom_equiv (β⁻¹_ X Y ≫ β_ X Y) (𝟙 _)
| braiding_naturality  {X X' Y Y' : ℕ} (f : X ⟶ᵐ Y) (g : X' ⟶ᵐ Y') : hom_equiv
    ((f ⊗ g) ≫ β_ Y Y') (β_ X X' ≫ (g ⊗ f))
| hexagon_forward {X Y Z} : hom_equiv
    (α_ X Y Z ≫ β_ X (Y + Z) ≫ α_ Y Z X)
    ((β_ X Y ⊗ 𝟙 Z) ≫ α_ Y X Z ≫ (𝟙 Y ⊗ β_ X Z))
| hexagon_reverse {X Y Z} : hom_equiv
    (α⁻¹_ X Y Z ≫ β_ (X + Y) Z ≫ α⁻¹_ Z X Y)
    ((𝟙 X ⊗ β_ Y Z) ≫ α⁻¹_ X Z Y ≫ (β_ X Z ⊗ 𝟙 Y))
| twist_hom_inv {X} : hom_equiv (θ_ X ≫ θ⁻¹_ X) (𝟙 _)
| twist_inv_hom {X} : hom_equiv (θ⁻¹_ X ≫ θ_ X) (𝟙 _)
| twist_naturality {X Y} (f : X ⟶ᵐ Y) : hom_equiv (f ≫ θ_ Y) (θ_ X ≫ f) 
| twist_braiding {X Y} : hom_equiv (θ_ (X + Y)) ((θ_ X ⊗ θ_ Y) ≫ β_ X Y ≫ β_ Y X)
| twist_left_dual {X} : hom_equiv (θ_ X)
    (ℓ⁻¹_ X ≫ (η_ X ⊗ 𝟙 _) ≫ ((𝟙 _ ⊗ θ_ X) ⊗ 𝟙 _) ≫ α_ X X X ≫ (𝟙 _ ⊗ ε_ X) ≫ ρ_ X)

end

open hom_equiv

def tangle_category : category ℕ :=
{ hom := λ X Y, quot (@hom_equiv X Y),
  id := λ X, quot.mk _ (id X),
  comp := λ X Y Z, 
  begin
    intros f g,
    rw quot.eq,
  end,
  -- quot.map₂ comp 
  --   (λ f g h, begin 
  --     intros H,
  --     rw quot.eq,
  --   refine hom_equiv.trans _ _,
  --   exact f.comp g,
  --   exact hom_equiv.refl _, 
  --   end)
  --   (λ _ _ _, comp_congr_left _ _ _),
  id_comp' := by { rintro X Y ⟨f⟩, exact quot.sound (id_comp f) },
  comp_id' := by { rintro X Y ⟨f⟩, exact quot.sound (comp_id f) },
  assoc' := by { rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩, exact quot.sound (assoc f g h) } }

local attribute [instance] tangle_category

local notation `⟦`:max a `⟧` := quot.mk (hom_equiv) a

def monoidal_category : monoidal_category ℕ :=
{ tensor_obj := λ X Y, X + Y,
  tensor_hom := λ _ _ _ _, quot.map₂ tensor
    (λ _, tensor_congr_right _)
    (λ _, tensor_congr_left _),
  tensor_id' := λ X Y, quot.sound tensor_id,
  tensor_comp' := λ X₁ Y₁ Z₁ X₂ Y₂ Z₂,
    by { rintros ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩, exact quot.sound (tensor_comp _ _ _ _) },
  tensor_unit := 0,
  associator := λ X Y Z,
    ⟨⟦associator_hom X Y Z⟧, ⟦associator_inv X Y Z⟧,
      quot.sound associator_hom_inv, quot.sound associator_inv_hom⟩,
  associator_naturality' := λ X₁ X₂ X₃ Y₁ Y₂ Y₃,
    by { rintros ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩, exact quot.sound (associator_naturality _ _ _) },
  left_unitor := λ X,
    ⟨⟦left_unitor_hom X⟧, ⟦left_unitor_inv X⟧,
      quot.sound left_unitor_hom_inv, quot.sound left_unitor_inv_hom⟩,
  left_unitor_naturality' := λ X Y, by { rintro ⟨f⟩, exact quot.sound (left_unitor_naturality _) },
  right_unitor := λ X,
    ⟨⟦right_unitor_hom X⟧, ⟦right_unitor_inv X⟧, 
      quot.sound right_unitor_hom_inv, quot.sound right_unitor_inv_hom⟩,
  right_unitor_naturality' := λ X Y, by { rintro ⟨f⟩, exact quot.sound (right_unitor_naturality _) },
  pentagon' := λ W X Y Z, quot.sound pentagon,
  triangle' := λ X Y, quot.sound triangle }

local attribute [instance] monoidal_category

def left_rigid_category : left_rigid_category ℕ :=
{ left_dual := λ X, 
  { left_dual := X,
    exact := 
    { coevaluation := ⟦coevaluation X⟧,
      evaluation := ⟦evaluation X⟧,
      coevaluation_evaluation' := quot.sound hom_equiv.coevaluation_evaluation,
      evaluation_coevaluation' := quot.sound hom_equiv.evaluation_coevaluation }}}

def braided_category : braided_category ℕ := 
{ braiding := λ X Y, 
  { hom := ⟦braiding_hom X Y⟧,
    inv := ⟦braiding_inv X Y⟧,
    hom_inv_id' := quot.sound hom_equiv.braiding_hom_inv,
    inv_hom_id' := quot.sound hom_equiv.braiding_inv_hom },
  braiding_naturality' := λ W X Y Z,
    by { rintro ⟨f⟩ ⟨g⟩, exact quot.sound (hom_equiv.braiding_naturality f g)},
  hexagon_forward' := λ X Y Z, quot.sound (hom_equiv.hexagon_forward),
  hexagon_reverse' := λ X Y Z, quot.sound (hom_equiv.hexagon_reverse) }

local attribute [instance] left_rigid_category
local attribute [instance] braided_category

/--
Examples of tangles.
-/
abbreviation cap : 0 ⟶ 2 := quot.mk _ (coevaluation 1)
abbreviation cup : 2 ⟶ 0 := quot.mk _ (evaluation 1)
abbreviation vert : 1 ⟶ 1 := quot.mk _ (hom.id 1)
abbreviation over : 2 ⟶ 2 := quot.mk _ (braiding_hom 1 1)
abbreviation under : 2 ⟶ 2 := quot.mk _ (braiding_inv 1 1)

#check cap
#check cup
#check vert
#check over
#check under
#check cap ≫ cup
#check α_ 2 1 3

open category_theory.monoidal_category

#check (vert ⊗ vert) ≫ (λ_ (1 + 1)).inv ≫ (cap ⊗ under) ≫ 
  (over ⊗ under) ≫ (α_ 2 1 1).inv ≫ (vert ⊗ vert ⊗ vert ⊗ vert)

#check cap ≫ cup

end tangle
