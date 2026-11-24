-- Prove2me | solution 1 for PI.ScPiFrameW.hJ_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:18:48.904049+00:00
-- url     : https://prove2.me/submissions/e9f820bc-835c-42ea-a0db-0a696a994362

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_HJSumSmulRight
import Theorems.Thm_PI_ScPiFrameW_hJ_eq_sum
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScPiFrameW
open PI.ScPiExists
variable {n : ℕ}
namespace PI.ScPiFrameW
theorem _root_.solution (ε : Fin n → Bool) (x : Fin n → ℂ) :
    hJ ε x x = ((∑ j, (if ε j then (1 : ℝ) else -1) * Complex.normSq (x j) : ℝ) : ℂ) := by
  rw [hJ_eq_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
  unfold sg
  split_ifs <;> simp
end PI.ScPiFrameW
