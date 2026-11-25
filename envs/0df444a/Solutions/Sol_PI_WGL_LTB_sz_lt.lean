-- Prove2me | solution 1 for PI.WGL.LTB.sz_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:08:43.868656+00:00
-- url     : https://prove2.me/submissions/fcdde0a2-61ea-4ad1-987c-78e096ea3077

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleB
import Theorems.Thm_PI_WGL_LTB_natW_last
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
theorem _root_.solution {n K : ℕ} (sg : DomWeight n) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (hsh : shapeDeg sz = sg.natW) (k : Fin K) (hk : 0 < sz k) : sz k < n := by
  have hn : 0 < n := lt_of_lt_of_le hk (hsz k)
  by_contra hcon
  have heq : sz k = n := le_antisymm (hsz k) (not_lt.mp hcon)
  have h1 := congrFun hsh ⟨n - 1, by omega⟩
  rw [natW_last sg hn] at h1
  unfold shapeDeg at h1
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1
  exact h1 (Finset.mem_univ k) (by simp; omega)
end PI.WGL.LTB
