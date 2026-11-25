-- Prove2me | solution 1 for PI.StabBigW.mul_g_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:38:27.946247+00:00
-- url     : https://prove2.me/submissions/1bab807a-5461-4b8f-9338-87ab15a55141

import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv
import Theorems.Thm_PI_StabBigW_wI_val
import Theorems.Thm_PI_StabBigW_g_mid_col
import Theorems.Thm_PI_StabBigW_g_wI
import Theorems.Thm_PI_StabBigW_sum_mid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabBigW
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
namespace PI.StabBigW
theorem _root_.solution (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i : Fin (2 * r + k + 1)) (t : Fin (k + 1)) :
    (A * bigCell k r c μ) i (wI k r t) = ∑ s, A i (wI k r s) * μ s t := by
  have htl := t.isLt
  rw [Matrix.mul_apply, sum_mid]
  · simp only [g_wI]
  · intro m hm
    rw [g_mid_col c μ m (wI k r t) (by rw [wI_val]; omega) (by rw [wI_val]; omega) hm, mul_zero]
end PI.StabBigW
