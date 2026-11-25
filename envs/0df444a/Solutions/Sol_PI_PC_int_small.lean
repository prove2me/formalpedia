-- Prove2me | solution 1 for PI.PC.int_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:31:49.330387+00:00
-- url     : https://prove2.me/submissions/69771301-b21f-46bd-9cb2-d984133e2866

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_ChebyshevPrimeBoundsLogFact
import Theorems.Thm_PI_PC_dyadic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PC
open Real MeasureTheory Set
namespace PI.PC
theorem _root_.solution : ∫ t in (2 : ℝ)..1024, phi t ≤ 61 := by
  have h := dyadic 9
  have h1024 : (2 : ℝ) ^ (9 + 1) = 1024 := by norm_num
  rw [h1024] at h
  have hs : ∑ i ∈ Finset.range 9, (2 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) ^ 2 ≤ 20.9 := by
    norm_num [Finset.sum_range_succ]
  have hl2 : 0.6931471803 < log 2 := Real.log_two_gt_d9
  have hb : 2 / log 2 * ∑ i ∈ Finset.range 9, (2 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) ^ 2 ≤ 61 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    linarith
  linarith
end PI.PC
