-- Prove2me | solution 1 for PI.lp_feasible_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:32:45.569875+00:00
-- url     : https://prove2.me/submissions/a88aec18-ad36-40f8-a893-8a0d07935eac

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LpLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LinearProgramLowerBound_LpFeasibleLe
import Theorems.Thm_PI_lp_shift_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI
open Finset
namespace PI
theorem _root_.solution (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) (hl : 2 ≤ l)
    {y : ℝ} (hy : y ∈ lpFeasible l d Ds) : y ≤ (∑ s, Ds s) / ((l : ℝ) + 1) := by
  obtain ⟨xs, h0, hsupp, hc, rfl⟩ := hy
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast (by omega : 1 ≤ l)
  have hsum : ∑ s, ((∑ i ∈ range d, (l : ℝ) ^ i * xs s i) +
      (∑ i ∈ range d, xs (s - (i : ZMod d)) i)) ≤ ∑ s, Ds s :=
    Finset.sum_le_sum fun s _ => hc s
  rw [Finset.sum_add_distrib, lp_shift_sum] at hsum
  have hlow : (l : ℝ) * ∑ s, ∑ i ∈ range d, xs s i ≤
      ∑ s, ∑ i ∈ range d, (l : ℝ) ^ i * xs s i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : Odd i
    · have hi0 : i ≠ 0 := by
        rintro rfl
        simp at hi
      exact mul_le_mul_of_nonneg_right (le_self_pow₀ hl1 hi0) (h0 s i)
    · rw [hsupp s i (Or.inl hi)]
      simp
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hsum, hlow]
end PI
