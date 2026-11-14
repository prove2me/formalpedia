-- Prove2me | solution 1 for SaglamGV.sMinus_bounds
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-13T10:22:41.158787+00:00
-- url     : https://prove2.me/submissions/6d5aaa01-e8f4-4d9e-9b37-f94005b70dde

import Definitions.Def_SaglamGV_Analytic

set_option autoImplicit false

private lemma tail_sum (z : ℝ) :
    HasSum (fun k : ℕ ↦ z ^ (2 * (k + 1) + 1) / ((2 * (k + 1) + 1).factorial : ℝ))
      (Real.sinh z - z) := by
  apply (hasSum_nat_add_iff
    (f := fun k : ℕ ↦ z ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) 1).2
  simpa using (Real.hasSum_sinh z)

private lemma cubic_bound (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.sinh z - z ≤ (Real.sinh 1 - 1) * z ^ 3 := by
  have hz := (tail_sum z).summable
  have h1 := ((tail_sum 1).mul_right (z ^ 3)).summable
  rw [← (tail_sum z).tsum_eq, ← ((tail_sum 1).mul_right (z ^ 3)).tsum_eq]
  apply hz.tsum_le_tsum _ h1
  intro k
  simp only [one_pow, one_div]
  rw [mul_comm _ (z ^ 3), ← div_eq_mul_inv]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact pow_le_pow_of_le_one hz0 hz1 (by omega)

theorem solution :
    (∀ z : ℝ, z ≤ 0 → SaglamGV.sMinus z ≤ 0) ∧
      (∀ z : ℝ, 0 ≤ z → z ≤ 1 →
        SaglamGV.sMinus z ≤ (Real.sinh 1 - 1) * z ^ 3) ∧
      (∀ z : ℝ, 1 ≤ z → SaglamGV.sMinus z ≤ 1 / 2 * Real.exp z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact sub_nonpos.mpr (Real.sinh_le_self_iff.mpr hz)
  · intro z hz0 hz1
    exact cubic_bound z hz0 hz1
  · intro z hz
    rw [SaglamGV.sMinus, Real.sinh_eq]
    have := Real.exp_pos (-z)
    linarith
