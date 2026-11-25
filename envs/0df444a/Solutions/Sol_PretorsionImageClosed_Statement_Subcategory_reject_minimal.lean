-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.reject_minimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:46:30.113158+00:00
-- url     : https://prove2.me/submissions/1f908c2f-2e79-420f-83bb-61bf3de27cdc

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_spec

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
variable (X)
namespace PretorsionImageClosed.Statement.Subcategory
theorem _root_.solution {K : Subobject X} (hK : F.prop (cokernel K.arrow)) (h : K ≤ F.reject X) :
    K = F.reject X :=
  (F.reject_spec X).2 K hK h
end PretorsionImageClosed.Statement.Subcategory
