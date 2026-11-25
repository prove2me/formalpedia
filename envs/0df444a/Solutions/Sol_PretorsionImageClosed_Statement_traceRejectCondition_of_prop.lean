-- Prove2me | solution 1 for PretorsionImageClosed.Statement.traceRejectCondition_of_prop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:00:01.905119+00:00
-- url     : https://prove2.me/submissions/b245a392-1aa5-4d61-9bfc-65bda5f28f82

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_bot_le
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_eq_bot_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_trace_iso


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
    (hX : F.prop X) : TraceRejectCondition T F X := by
  have hr : F.reject X = ⊥ := (reject_eq_bot_iff hF).2 hX
  have h1 : F.reject X ≤ T.trace X := by rw [hr]; exact bot_le
  refine ⟨h1, ?_, ?_⟩
  · have ht : F.prop (T.trace X : C) := hF (T.trace X).arrow inferInstance hX
    rw [(reject_eq_bot_iff hF).2 ht]
    symm
    rw [Subobject.mk_eq_bot_iff_zero, ← cancel_mono (T.trace X).arrow, Subobject.ofLE_arrow,
      zero_comp, hr, Subobject.bot_arrow]
  · have key : ∀ r : Subobject X, r = ⊥ →
        T.trace (cokernel r.arrow) = imageSubobject ((T.trace X).arrow ≫ cokernel.π r.arrow) := by
      rintro _ rfl
      haveI : IsIso (cokernel.π (⊥ : Subobject X).arrow) := cokernel.π_of_zero Subobject.bot_arrow
      rw [trace_iso hT (asIso (cokernel.π (⊥ : Subobject X).arrow)), imageSubobject_mono]
      rfl
    exact key _ hr
end PretorsionImageClosed.Statement
