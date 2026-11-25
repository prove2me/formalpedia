-- Prove2me | solution 1 for PI.WGL.LTB.top_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:08:46.193026+00:00
-- url     : https://prove2.me/submissions/3c8088b7-7f35-432b-b6c6-f7b27dfd3964

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleB
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTM
namespace PI.WGL.LTB
theorem _root_.solution {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (J : ∀ k, Fin (sz k) → Fin n)
    (hinj : ∀ k, Function.Injective (J k)) (hlt : ∀ k p, (J k p).1 < sz k) :
    ∀ k, ∃ σ : Equiv.Perm (Fin (sz k)), J k = stdT sz hsz k ∘ σ := by
  intro k
  let f : Fin (sz k) → Fin (sz k) := fun p => ⟨(J k p).1, hlt k p⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply hinj k
    exact Fin.ext (by simpa [f] using congrArg Fin.val hab)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), ?_⟩
  funext p
  exact Fin.ext rfl
end PI.WGL.LTB
