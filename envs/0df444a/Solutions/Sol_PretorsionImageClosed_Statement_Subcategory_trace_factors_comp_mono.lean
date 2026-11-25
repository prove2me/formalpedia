-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.trace_factors_comp_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:53:48.550319+00:00
-- url     : https://prove2.me/submissions/22412b20-b971-4ad3-854e-566907093c56

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
theorem _root_.solution (hT : T.IsQuotientClosed) {W : C} (f : W ⟶ X) [Mono f] :
    (T.trace X).Factors ((T.trace W).arrow ≫ f) :=
  trace_factors hT _ (T.prop_trace W)
end PretorsionImageClosed.Statement.Subcategory
