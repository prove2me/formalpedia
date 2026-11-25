-- Prove2me | solution 1 for PI.EF.le_exp_Mfun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:31.996251+00:00
-- url     : https://prove2.me/submissions/1905afa9-d56e-48e8-b45a-a88722ee98ef

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_HalfLeNormLentCtr
import Theorems.Thm_PI_EF_two_le_arg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Metric Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]
namespace PI.EF
theorem _root_.solution {A C : ℝ} (hC : 0 < C) (N : ℕ) [NeZero N] (t : ℝ) :
    2 * C * (4 * (N * (|t| + 2))) ^ A ≤ Real.exp (Mfun A C N t) := by
  unfold Mfun
  have hY : (0 : ℝ) < 4 * (N * (|t| + 2)) := by linarith [two_le_arg N t]
  rw [Real.exp_add, Real.rpow_def_of_pos hY, mul_comm (Real.log (4 * (N * (|t| + 2)))) A]
  have h2C : 2 * C ≤ Real.exp |Real.log (2 * C)| := by
    calc 2 * C = Real.exp (Real.log (2 * C)) := (Real.exp_log (by linarith)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (le_abs_self _)
  exact mul_le_mul_of_nonneg_right h2C (Real.exp_pos _).le
end PI.EF
