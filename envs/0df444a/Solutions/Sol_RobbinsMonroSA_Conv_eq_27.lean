-- Prove2me | solution 1 for RobbinsMonroSA.Conv.eq_27
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-06T21:21:06.78243+00:00
-- url     : https://prove2.me/submissions/4e032040-5b79-4831-a65f-1df5ade6f5e5

import Mathlib
import Definitions.Def_RobbinsMonroSA_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open RobbinsMonroSA.Conv

/-- (26) ⇒ (27): positive steps with divergent weighted ratios force `Σ a_n = ∞`. -/
theorem solution (a : ℕ → ℝ) (hpos : ∀ n, 0 < a n) (h26 : StepCond26 a) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop atTop := by
  -- Ratio terms appearing in (26)
  set r : ℕ → ℝ := fun n =>
    a (n + 1) / ∑ i ∈ Finset.range (n + 1), a i
  have hr_nonneg : ∀ n, 0 ≤ r n := by
    intro n
    exact div_nonneg (hpos _).le (Finset.sum_nonneg fun i _ => (hpos i).le)
  -- Unfold (26) onto `r`
  have h26' : Tendsto (fun N => ∑ n ∈ Finset.range N, r n) atTop atTop := by
    unfold StepCond26 at h26
    simpa [r] using h26
  -- (26) ⇒ ¬Summable r
  have hr_not : ¬Summable r :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hr_nonneg).2 h26'
  -- If `a` were summable, comparison would force `r` summable — contradiction
  have ha_not : ¬Summable a := by
    intro ha
    have hS_ge : ∀ n, a 0 ≤ ∑ i ∈ Finset.range (n + 1), a i := by
      intro n
      calc
        a 0 = ∑ i ∈ Finset.range 1, a i := by simp
        _ ≤ ∑ i ∈ Finset.range (n + 1), a i :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (Nat.le_add_left 1 n))
            (fun i _ _ => (hpos i).le)
    have hr_le : ∀ n, r n ≤ a (n + 1) / a 0 := by
      intro n
      dsimp [r]
      exact div_le_div_of_nonneg_left (hpos _).le (hpos 0) (hS_ge n)
    have hshift : Summable fun n => a (n + 1) := (summable_nat_add_iff 1).2 ha
    have hbound : Summable fun n => a (n + 1) / a 0 := by
      simpa [div_eq_mul_inv] using hshift.mul_right (a 0)⁻¹
    exact hr_not (Summable.of_nonneg_of_le hr_nonneg hr_le hbound)
  -- ¬Summable a ⇒ partial sums → ∞
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => (hpos n).le)).1 ha_not
