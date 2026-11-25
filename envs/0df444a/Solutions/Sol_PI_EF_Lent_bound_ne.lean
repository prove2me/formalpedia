-- Prove2me | solution 1 for PI.EF.Lent_bound_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:36:57.367154+00:00
-- url     : https://prove2.me/submissions/71b6ca91-8a62-48c8-a07c-58661a493716

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_HalfLeNormLentCtr
import Theorems.Thm_PI_EF_one_le_level
import Theorems.Thm_PI_EF_Lent_eq

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
theorem _root_.solution {A C : ℝ} (hA : 0 < A) (hC : 0 < C) (hG : LGrowth A C)
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {t : ℝ} {z : ℂ} (h1 : -4 ≤ z.re)
    (h2 : z.re ≤ 8) (h3 : |z.im| ≤ |t| + 6) (hz : z ≠ 1) :
    ‖Lent χ z‖ ≤ C * (4 * (N * (|t| + 2))) ^ A := by
  rw [Lent_eq χ hz]
  refine (hG N χ hχ z h1 h2).trans ?_
  have hN := one_le_level N
  have hb : (N : ℝ) * (|z.im| + 2) ≤ 4 * (N * (|t| + 2)) := by
    have := mul_le_mul_of_nonneg_left (show |z.im| + 2 ≤ 4 * (|t| + 2) by linarith [abs_nonneg t])
      (show (0 : ℝ) ≤ N by linarith)
    linarith
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb hA.le) hC.le
end PI.EF
