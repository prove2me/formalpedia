-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsTrivial.biprod_desc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:17:25.696527+00:00
-- url     : https://prove2.me/submissions/d6cc3b3e-ae16-4d94-9267-c7aba5501ee0

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
namespace IsTrivial
theorem _root_.solution {X₁ X₂ Y : C} {f₁ : X₁ ⟶ Y} {f₂ : X₂ ⟶ Y}
    (h₁ : IsTrivial Zs.prop f₁) (h₂ : IsTrivial Zs.prop f₂) :
    IsTrivial Zs.prop (biprod.desc f₁ f₂) := by
  obtain ⟨W₁, hW₁, g₁, k₁, rfl⟩ := h₁
  obtain ⟨W₂, hW₂, g₂, k₂, rfl⟩ := h₂
  refine ⟨W₁ ⊞ W₂, Zs.prop_biprod hW₁ hW₂, biprod.map g₁ g₂, biprod.desc k₁ k₂, ?_⟩
  apply biprod.hom_ext' <;> simp
end IsTrivial
end PretorsionImageClosed.Statement
