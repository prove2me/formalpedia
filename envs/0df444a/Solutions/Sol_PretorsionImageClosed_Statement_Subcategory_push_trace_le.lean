-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.push_trace_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:54:12.03161+00:00
-- url     : https://prove2.me/submissions/8d6a9c24-98e5-4bad-b6fd-c5b82fdebafa

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
open PretorsionImageClosed PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C] [HasLength C] {T F : Subcategory C}
namespace PretorsionImageClosed.Statement.Subcategory
theorem _root_.solution (hT : T.IsQuotientClosed) {X : C} (W : Subobject X) :
    Subobject.push W (T.trace (W : C)) ≤ T.trace X :=
  le_trace hT (T.prop_of_iso (Subobject.underlyingIso _).symm (T.prop_trace _))
end PretorsionImageClosed.Statement.Subcategory
