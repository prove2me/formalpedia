-- Prove2me | solution 1 for PretorsionImageClosed.Statement.reject_coe_eq_mk_ofLE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:58.396805+00:00
-- url     : https://prove2.me/submissions/8ecfed5d-fd24-4b04-8ba3-01b3451d450e

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_iso


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C] {T F : Subcategory C} {X : C}
namespace PretorsionImageClosed.Statement
theorem _root_.solution (hF : F.IsSubobjectClosed) {t r : Subobject X} (h : r ≤ t)
    {A B : C} (ι : A ⟶ X) [Mono ι] (κ : B ⟶ A) [Mono κ] (ht : t = Subobject.mk ι)
    (hr : r = Subobject.mk (κ ≫ ι)) (hA : F.reject A = Subobject.mk κ) :
    F.reject (t : C) = Subobject.mk (Subobject.ofLE r t h) := by
  subst ht hr
  rw [reject_iso hF (Subobject.underlyingIso ι).symm, hA]
  symm
  apply Subobject.mk_eq_mk_of_comm _ _
    ((Subobject.underlyingIso (κ ≫ ι)).trans (Subobject.underlyingIso κ).symm)
  rw [← cancel_mono (Subobject.mk ι).arrow, Category.assoc, Subobject.ofLE_arrow, Iso.trans_hom,
    Iso.symm_hom, Iso.symm_hom, Category.assoc, Category.assoc, Subobject.underlyingIso_arrow,
    ← Category.assoc (Subobject.underlyingIso κ).inv, Subobject.underlyingIso_arrow,
    Subobject.underlyingIso_hom_comp_eq_mk]
end PretorsionImageClosed.Statement
