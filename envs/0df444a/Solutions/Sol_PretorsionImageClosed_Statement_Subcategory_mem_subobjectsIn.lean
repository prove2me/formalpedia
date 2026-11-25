-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.mem_subobjectsIn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:50:23.702856+00:00
-- url     : https://prove2.me/submissions/ebc2b57d-b498-42aa-a7bb-514032f8e394

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
namespace PretorsionImageClosed.Statement.Subcategory
theorem _root_.solution {S : Subobject X} : S ∈ T.subobjectsIn X ↔ T.prop (S : C) := Iff.rfl
end PretorsionImageClosed.Statement.Subcategory
