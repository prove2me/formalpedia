-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.pb_mul_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:55:21.863243+00:00
-- url     : https://prove2.me/submissions/5e038577-a21a-4121-a5fc-bb9f60e6559b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBB

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
theorem _root_.solution (A A' : B.Mat k r) : ‖A * A'‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (‖A‖ * ‖A'‖) := by
  rw [Matrix.norm_le_iff (by positivity)]
  intro i j
  rw [Matrix.mul_apply]
  calc ‖∑ l, A i l * A' l j‖ ≤ ∑ l, ‖A i l * A' l j‖ := norm_sum_le _ _
    _ ≤ ∑ _l : Fin (2 * r + k + 1), ‖A‖ * ‖A'‖ := Finset.sum_le_sum fun l _ => by
        rw [norm_mul]
        exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A)
          (Matrix.norm_entry_le_entrywise_sup_norm A') (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp
end PI.UnitaryCorollaryDerivatives
