-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.trace_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:52:22.321012+00:00
-- url     : https://prove2.me/submissions/9797d329-b610-4982-a3f6-23c624719f86

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
variable [HasLength C]
variable {T X}
namespace PretorsionImageClosed.Statement.Subcategory
theorem _root_.solution (hT : T.IsQuotientClosed) {S : Subobject X} :
    T.trace X ≤ S ↔ ∀ {Y : C} (f : Y ⟶ X), T.prop Y → S.Factors f :=
  ⟨fun h _ f hY => Subobject.factors_of_le f h (trace_factors hT f hY),
   fun h => Subobject.le_of_factors (h _ (T.prop_trace X))⟩
end PretorsionImageClosed.Statement.Subcategory
