-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.trace_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:39:40.938736+00:00
-- url     : https://prove2.me/submissions/a0140bd7-8655-4747-aece-dfc331137a89

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveB

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
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.DjC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable {N j : ℕ}
namespace PI.UnitaryCorollaryDerivatives.DjC
theorem _root_.solution (e : Fin j ↪ Fin N) (Y : Matrix (Fin N) (Fin N) ℂ) : ‖(sub e Y).trace‖ ≤ (j : ℝ) * mx Y := by
  unfold mx
  simp only [Matrix.trace, Matrix.diag]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ a, ‖sub e Y a a‖ ≤ ∑ _a : Fin j, ‖Matrix.of.symm Y‖ := Finset.sum_le_sum fun a _ => by
        show ‖Y (e a) (e a)‖ ≤ _
        exact (norm_le_pi_norm (Matrix.of.symm Y (e a)) (e a)).trans (norm_le_pi_norm (Matrix.of.symm Y) (e a))
    _ = (j : ℝ) * ‖Matrix.of.symm Y‖ := by simp
end PI.UnitaryCorollaryDerivatives.DjC
