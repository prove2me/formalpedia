-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.isQuotientClosed_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:46:44.194012+00:00
-- url     : https://prove2.me/submissions/8e275a32-0c63-4fcc-bedf-022fba57faa3

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement ZeroObject
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
open PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
variable (Z : Subcategory C)
namespace PretorsionImageClosed.Statement.Subcategory
theorem _root_.solution : (⊥ : Subcategory C).IsQuotientClosed := by
  intro X Y f hf hX
  change IsZero Y
  rw [IsZero.iff_id_eq_zero, ← cancel_epi f, comp_zero, hX.eq_zero_of_src (f ≫ 𝟙 Y)]
end PretorsionImageClosed.Statement.Subcategory
