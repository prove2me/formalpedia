-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.top_mem_subobjectsIn_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:41:41.610793+00:00
-- url     : https://prove2.me/submissions/9ddec263-0ac2-4115-b6c3-55ec404d96ae

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
namespace PretorsionImageClosed.Statement.Subcategory
theorem _root_.solution : ⊤ ∈ T.subobjectsIn X ↔ T.prop X :=
  T.prop_iff_of_iso (asIso (⊤ : Subobject X).arrow)
end PretorsionImageClosed.Statement.Subcategory
