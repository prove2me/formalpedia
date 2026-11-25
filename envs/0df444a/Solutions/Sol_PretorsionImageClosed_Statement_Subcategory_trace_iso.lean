-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.trace_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:29:42.427088+00:00
-- url     : https://prove2.me/submissions/edf7d973-30c2-46f1-957a-65cb539aa97a

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
theorem _root_.solution (hT : T.IsQuotientClosed) {X Y : C} (e : X ≅ Y) :
    T.trace Y = Subobject.mk ((T.trace X).arrow ≫ e.hom) := by
  apply le_antisymm
  · have hS : T.prop (Subobject.mk ((T.trace Y).arrow ≫ e.inv) : C) :=
      T.prop_of_iso (Subobject.underlyingIso _).symm (T.prop_trace Y)
    have hle := le_trace hT hS
    refine Subobject.le_mk_of_comm
      ((Subobject.underlyingIso ((T.trace Y).arrow ≫ e.inv)).inv ≫ Subobject.ofLE _ _ hle) ?_
    rw [Category.assoc, ← Category.assoc (Subobject.ofLE _ _ hle), Subobject.ofLE_arrow,
      ← Category.assoc, Subobject.underlyingIso_arrow, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  · exact le_trace hT (T.prop_of_iso (Subobject.underlyingIso _).symm (T.prop_trace X))
end PretorsionImageClosed.Statement.Subcategory
