-- Prove2me | solution 1 for PretorsionImageClosed.Statement.traceRejectCondition_of_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:05:01.825369+00:00
-- url     : https://prove2.me/submissions/b6cc721d-c418-4695-b5fa-92b6c274dd97

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_iso
public import Theorems.Thm_PretorsionImageClosed_Subobject_eq_of_isZero


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C] {T F : Subcategory C} {X : C}
namespace PretorsionImageClosed.Statement
theorem _root_.solution (hT : T.IsQuotientClosed) (hF : F.IsSubobjectClosed)
    (hr : F.reject X = ⊤) (ht : T.trace X = ⊤) : TraceRejectCondition T F X := by
  have h1 : F.reject X ≤ T.trace X := by rw [hr, ht]
  refine ⟨h1, ?_, ?_⟩
  · have key : ∀ (t r : Subobject X) (h : r ≤ t), t = ⊤ → r = ⊤ →
        F.reject (t : C) = Subobject.mk (Subobject.ofLE r t h) := by
      rintro _ _ h rfl rfl
      haveI : IsIso (Subobject.ofLE (⊤ : Subobject X) ⊤ h) := by
        rw [Subobject.ofLE_refl]
        infer_instance
      rw [Subobject.mk_eq_top_of_isIso, reject_iso hF (asIso (⊤ : Subobject X).arrow).symm, hr]
      exact Subobject.mk_eq_top_of_isIso _
    exact key _ _ h1 ht hr
  · have key : ∀ r : Subobject X, r = ⊤ →
        T.trace (cokernel r.arrow) = imageSubobject ((T.trace X).arrow ≫ cokernel.π r.arrow) := by
      rintro _ rfl
      exact Subobject.eq_of_isZero (isZero_zero C |>.of_iso (cokernel.ofEpi _)) _ _
    exact key _ hr
end PretorsionImageClosed.Statement
