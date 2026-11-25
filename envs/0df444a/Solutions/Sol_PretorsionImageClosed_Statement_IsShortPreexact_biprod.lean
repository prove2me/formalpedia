-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsShortPreexact.biprod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:02:13.729516+00:00
-- url     : https://prove2.me/submissions/8c945d6d-058b-453a-a95e-c35ef60bd860

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Pretorsion_DirectSums

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C] {Zs : Subcategory C}
namespace PretorsionImageClosed.Statement
namespace IsShortPreexact
theorem _root_.solution {T₁ X₁ F₁ T₂ X₂ F₂ : C} {u₁ : T₁ ⟶ X₁} {v₁ : X₁ ⟶ F₁}
    {u₂ : T₂ ⟶ X₂} {v₂ : X₂ ⟶ F₂} (h₁ : IsShortPreexact Zs.prop u₁ v₁)
    (h₂ : IsShortPreexact Zs.prop u₂ v₂) :
    IsShortPreexact Zs.prop (biprod.map u₁ u₂) (biprod.map v₁ v₂) :=
  ⟨h₁.1.biprod h₂.1, h₁.2.biprod h₂.2⟩
end IsShortPreexact
end PretorsionImageClosed.Statement
