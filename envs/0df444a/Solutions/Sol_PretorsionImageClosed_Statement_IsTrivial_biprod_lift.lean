-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsTrivial.biprod_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:17:01.870328+00:00
-- url     : https://prove2.me/submissions/985fe0d7-baa0-486c-91f5-018dca1de9bd

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
theorem _root_.solution {W Y₁ Y₂ : C} {f₁ : W ⟶ Y₁} {f₂ : W ⟶ Y₂}
    (h₁ : IsTrivial Zs.prop f₁) (h₂ : IsTrivial Zs.prop f₂) :
    IsTrivial Zs.prop (biprod.lift f₁ f₂) := by
  obtain ⟨W₁, hW₁, g₁, k₁, rfl⟩ := h₁
  obtain ⟨W₂, hW₂, g₂, k₂, rfl⟩ := h₂
  refine ⟨W₁ ⊞ W₂, Zs.prop_biprod hW₁ hW₂, biprod.lift g₁ g₂, biprod.map k₁ k₂, ?_⟩
  apply biprod.hom_ext <;> simp
end IsTrivial
end PretorsionImageClosed.Statement
