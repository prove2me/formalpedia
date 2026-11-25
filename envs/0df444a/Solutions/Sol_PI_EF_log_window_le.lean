-- Prove2me | solution 1 for PI.EF.log_window_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:46.76397+00:00
-- url     : https://prove2.me/submissions/d480d42d-5100-46ef-bd5a-ee5a6f8e771a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormSubCtrSq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ExplicitFormulaFromGluing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogWindowLe

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
theorem _root_.solution (N : ℕ) [NeZero N] {t u : ℝ} (hu : |u| ≤ |t| + 2) :
    Real.log (N * (|u| + 2)) ≤ 2 * LL N t := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have ht := abs_nonneg t
  have hu0 := abs_nonneg u
  rw [LL.eq_1]
  have hpos : 0 < (N : ℝ) * (|u| + 2) := by positivity
  have h1 : (N : ℝ) * (|u| + 2) ≤ N * (|t| + 4) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : |t| + 4 ≤ (|t| + 2) ^ 2 := by nlinarith
  have h3 : (N : ℝ) * (|t| + 4) ≤ (N : ℝ) ^ 2 * (|t| + 2) ^ 2 := by
    calc (N : ℝ) * (|t| + 4) ≤ (N : ℝ) ^ 2 * (|t| + 4) :=
          mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
      _ ≤ (N : ℝ) ^ 2 * (|t| + 2) ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
  calc Real.log (N * (|u| + 2)) ≤ Real.log ((N * (|t| + 2)) ^ 2) :=
        Real.log_le_log hpos (by rw [mul_pow]; linarith)
    _ = 2 * Real.log (N * (|t| + 2)) := by rw [Real.log_pow]; norm_num
end PI.EF
