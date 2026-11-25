-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.isSubobjectClosed_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:21:57.526377+00:00
-- url     : https://prove2.me/submissions/fc406be1-d254-46fd-b780-96140fde2799

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
theorem _root_.solution : (⊥ : Subcategory C).IsSubobjectClosed := by
  intro X Y f hf hY
  change IsZero X
  rw [IsZero.iff_id_eq_zero, ← cancel_mono f, zero_comp, hY.eq_zero_of_tgt (𝟙 X ≫ f)]
end PretorsionImageClosed.Statement.Subcategory
