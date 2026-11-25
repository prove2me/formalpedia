-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.prop_cokernel_reject
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:37:45.922525+00:00
-- url     : https://prove2.me/submissions/c98b4c4d-cad8-4bb7-aa11-cc8a684fffc7

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
theorem _root_.solution : F.prop (cokernel (F.reject X).arrow) := (F.reject_spec X).1
end PretorsionImageClosed.Statement.Subcategory
