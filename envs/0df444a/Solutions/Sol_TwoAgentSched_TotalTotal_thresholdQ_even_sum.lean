-- Prove2me | solution 1 for TwoAgentSched.TotalTotal.thresholdQ_even_sum
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:11:52.68096+00:00
-- url     : https://prove2.me/submissions/e9e3a3d1-b12d-453c-b818-ef7118bc0c6b

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_Construction

set_option autoImplicit false

namespace TwoAgentSched.TotalTotal

/-- Integer threshold expressed as a sum of nonnegative multiples of half the
    even job lengths. This form can be accumulated by repeated binary addition. -/
def thresholdAccumulator {k : ℕ} (p : Fin k → ℕ) : ℕ :=
  ∑ i : Fin k, (4 * (k - (i.val + 1)) + 3) * (p i / 2)

/-- For even job lengths the accumulator equals the paper's real threshold. -/
theorem thresholdAccumulator_correct {k : ℕ} (p : Fin k → ℕ) (he : ∀ i, Even (p i)) :
    thresholdQ p = (thresholdAccumulator p : ℝ) := by
  have hp (i : Fin k) : p i = 2 * (p i / 2) := by
    obtain ⟨m, hm⟩ := he i
    omega
  have hpR (i : Fin k) : (p i : ℝ) = 2 * ((p i / 2 : ℕ) : ℝ) := by
    exact_mod_cast hp i
  unfold thresholdQ thresholdAccumulator bigP weightedSum
  push_cast
  simp_rw [hpR]
  have hpoint (i : Fin k) :
      (4 * ((k - (i.val + 1) : ℕ) : ℝ) + 3) * ((p i / 2 : ℕ) : ℝ) =
        3 * ((p i / 2 : ℕ) : ℝ) +
          2 * (((k - (i.val + 1) : ℕ) : ℝ) * (2 * ((p i / 2 : ℕ) : ℝ))) := by ring
  simp_rw [hpoint]
  simp only [Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Each accumulator coefficient is linearly bounded in the job count. -/
theorem thresholdAccumulator_coefficient_le {k : ℕ} (i : Fin k) :
    4 * (k - (i.val + 1)) + 3 ≤ 4 * k + 3 := by omega

end TwoAgentSched.TotalTotal

open TwoAgentSched.TotalTotal

theorem solution {k : ℕ} (p : Fin k → ℕ) (he : ∀ i, Even (p i)) :
    thresholdQ p = ((∑ i : Fin k, (4 * (k - (i.val + 1)) + 3) * (p i / 2) : ℕ) : ℝ) := by
  simpa [thresholdAccumulator] using thresholdAccumulator_correct p he
