-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.pb_dirL_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:36.122648+00:00
-- url     : https://prove2.me/submissions/defe260d-db07-499e-8c87-d2ac67b197e1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBB
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_mul_norm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution {x : Bool × B.Mat k r} (hx : B.unitLie k r x.2) (g : B.Mat k r) :
    ‖dirL x g‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * ‖g‖ := by
  have hX : ‖x.2‖ ≤ 1 := (Matrix.norm_le_iff zero_le_one).2 hx.2
  unfold dirL
  split_ifs
  · show ‖-x.2 * g‖ ≤ _
    calc ‖-x.2 * g‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (‖-x.2‖ * ‖g‖) := pb_mul_norm_le _ _
      _ ≤ _ := by
        rw [norm_neg]
        exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) hX) (by positivity)
  · first
    | show ‖g * x.2‖ ≤ _
      calc ‖g * x.2‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (‖g‖ * ‖x.2‖) := pb_mul_norm_le _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (norm_nonneg _) hX) (by positivity)
    | (unfold mulRightRealCLM; done)
end PI.UnitaryCorollaryDerivatives
