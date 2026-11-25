-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.mem_quotientsIn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:52:10.585509+00:00
-- url     : https://prove2.me/submissions/b2fd73e8-26c8-4609-a75f-1ce120a8c30a

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace

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
theorem _root_.solution {K : Subobject X} : K ∈ F.quotientsIn X ↔ F.prop (cokernel K.arrow) :=
  Iff.rfl
end PretorsionImageClosed.Statement.Subcategory
