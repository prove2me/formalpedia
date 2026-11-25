-- Prove2me | solution 1 for PI.WGL.XiU.normSq_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:11:49.741092+00:00
-- url     : https://prove2.me/submissions/fea75062-98b3-47d9-853a-7ec1005a6203

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_MultisetProdNormLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.XiU
open Matrix
namespace PI.WGL.XiU
theorem _root_.solution {N : ℕ} (u : Fin N → ℂ) :
    star u ⬝ᵥ u = ((∑ a, Complex.normSq (u a) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
end PI.WGL.XiU
