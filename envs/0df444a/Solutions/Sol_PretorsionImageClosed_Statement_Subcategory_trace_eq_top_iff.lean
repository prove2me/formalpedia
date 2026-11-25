-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.trace_eq_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:49:24.718124+00:00
-- url     : https://prove2.me/submissions/b3ff91b2-7793-4952-a1e1-0166b8e320d3

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_top_mem_subobjectsIn_iff

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
variable [HasLength C]
variable {T X}
namespace PretorsionImageClosed.Statement.Subcategory
theorem _root_.solution (hT : T.IsQuotientClosed) : T.trace X = ⊤ ↔ T.prop X :=
  ⟨fun h => (T.top_mem_subobjectsIn_iff X).1 (h ▸ T.prop_trace X),
   fun h => top_le_iff.1 (le_trace hT ((T.top_mem_subobjectsIn_iff X).2 h))⟩
end PretorsionImageClosed.Statement.Subcategory
