-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.bot_mem_quotientsIn_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:42:13.20281+00:00
-- url     : https://prove2.me/submissions/44f6d735-228f-40d2-b475-409f75a613a2

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_iff_of_iso


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement ZeroObject
variable {C : Type*} [Category C] [Abelian C]
open PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
variable (T : Subcategory C) (X : C)
variable (F : Subcategory C)
namespace PretorsionImageClosed.Statement.Subcategory
theorem _root_.solution : ⊥ ∈ F.quotientsIn X ↔ F.prop X := by
  change F.prop (cokernel (⊥ : Subobject X).arrow) ↔ F.prop X
  rw [Subobject.bot_arrow]
  exact F.prop_iff_of_iso cokernelZeroIsoTarget
end PretorsionImageClosed.Statement.Subcategory
