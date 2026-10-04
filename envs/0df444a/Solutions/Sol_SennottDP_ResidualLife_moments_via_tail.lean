-- Prove2me | solution 1 for SennottDP.ResidualLife.moments_via_tail
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T19:39:23.846061+00:00
-- url     : https://prove2.me/submissions/4fc9028f-c19d-44f5-b2d5-a7a047d9be0c

import Mathlib
import Definitions.Def_SennottDP_ResidualLife_MSDist

open scoped ENNReal NNReal

open SennottDP.ResidualLife in
theorem p7fb_tail_swap (u : ℕ → ℝ≥0∞) (g : ℕ → ℝ≥0∞) :
    ∑' y, g y * tail u y = ∑' w, (∑ y ∈ Finset.range w, g y) * u w := by
  unfold tail
  have h1 : ∀ y, g y * ∑' w : ℕ, (if y < w then u w else 0)
      = ∑' w : ℕ, (if y < w then g y * u w else 0) := by
    intro y
    rw [← ENNReal.tsum_mul_left]
    congr 1; funext w; split_ifs <;> simp
  simp_rw [h1]
  rw [ENNReal.tsum_comm]
  congr 1; funext w
  rw [tsum_eq_sum (s := Finset.range w)]
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro y hy
    rw [if_pos (Finset.mem_range.mp hy)]
  · intro y hy
    rw [if_neg]
    simpa [Finset.mem_range] using hy

theorem p7fb_nat_id (k : ℕ) : ∀ w : ℕ, 1 ≤ w →
    w ^ k = 1 + ∑ z ∈ Finset.range k, Nat.choose k z *
      ∑ y ∈ Finset.range w, (if 1 ≤ y then y ^ z else 0) := by
  intro w hw
  induction w, hw using Nat.le_induction with
  | base => simp
  | succ w hw ih =>
    have hadd : (w + 1) ^ k = w ^ k + ∑ z ∈ Finset.range k, Nat.choose k z * w ^ z := by
      rw [add_pow, Finset.sum_range_succ]
      simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_id]
      have hc : ∀ z ∈ Finset.range k, w ^ z * Nat.choose k z = Nat.choose k z * w ^ z :=
        fun z _ => mul_comm _ _
      rw [Finset.sum_congr rfl hc, add_comm]
    rw [hadd, ih]
    simp only [Finset.sum_range_succ, if_pos hw, mul_add, Finset.sum_add_distrib]
    ring

open SennottDP.ResidualLife ENNReal in
theorem solution (u : ℕ → ℝ≥0∞) (hu : IsDistOnPos u) :
    moment u 1 = ∑' y, tail u y ∧
    ∀ k : ℕ, 2 ≤ k →
      moment u k = 1 + ∑ z ∈ Finset.range k,
        (Nat.choose k z : ℝ≥0∞) * ∑' y : ℕ, (if 1 ≤ y then (y : ℝ≥0∞) ^ z * tail u y else 0) := by
  obtain ⟨hsum, hu0⟩ := hu
  constructor
  · have := p7fb_tail_swap u (fun _ => 1)
    simp only [one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
    rw [this]
    unfold moment
    congr 1; funext w; simp
  · intro k _
    unfold moment
    have hpt : ∀ w : ℕ, (w : ℝ≥0∞) ^ k * u w =
        u w + ∑ z ∈ Finset.range k, (Nat.choose k z : ℝ≥0∞) *
          ((∑ y ∈ Finset.range w, (if 1 ≤ y then (y : ℝ≥0∞) ^ z else 0)) * u w) := by
      intro w
      rcases Nat.eq_zero_or_pos w with rfl | hw
      · simp [hu0]
      · have h := p7fb_nat_id k w hw
        have hc : ((w ^ k : ℕ) : ℝ≥0∞) = ((1 + ∑ z ∈ Finset.range k, Nat.choose k z *
            ∑ y ∈ Finset.range w, (if 1 ≤ y then y ^ z else 0) : ℕ) : ℝ≥0∞) := by rw [← h]
        push_cast at hc
        rw [hc, add_mul, one_mul, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl ?_
        intro z _
        ring
    simp_rw [hpt]
    rw [ENNReal.tsum_add, hsum, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro z _
    rw [ENNReal.tsum_mul_left]
    congr 1
    rw [← p7fb_tail_swap]
    congr 1; funext y
    split_ifs <;> simp
