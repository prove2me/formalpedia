-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.pb_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:14:23.651607+00:00
-- url     : https://prove2.me/submissions/fd3da0c5-eedc-4da5-a014-6124ef78a407

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBB
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_sup_le_gN
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_dirL_le
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_Dw_clm

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
theorem _root_.solution (Λ : B.Mat k r →L[ℝ] ℂ) (hΛ : ∀ g, ‖Λ g‖ ≤ 1 * ‖g‖) : PG 1 (fun g => Λ g) := by
  refine ⟨Λ.contDiff, fun n => ?_⟩
  have hK1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  refine ⟨((2 * r + k + 1 : ℕ) : ℝ) ^ n, fun w hw hn g _ => ?_⟩
  obtain ⟨Λ', hΛ', hb⟩ := pb_Dw_clm (by linarith) w (fun x hx g => pb_dirL_le (hw x hx) g)
    Λ 1 zero_le_one hΛ
  rw [hΛ', Real.rpow_one]
  calc ‖Λ' g‖ ≤ 1 * ((2 * r + k + 1 : ℕ) : ℝ) ^ w.length * ‖g‖ := hb g
    _ ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ n * B.gN g := by
      rw [one_mul]
      exact mul_le_mul (pow_le_pow_right₀ hK1 hn) (pb_sup_le_gN g) (norm_nonneg _) (by positivity)
end PI.UnitaryCorollaryDerivatives
