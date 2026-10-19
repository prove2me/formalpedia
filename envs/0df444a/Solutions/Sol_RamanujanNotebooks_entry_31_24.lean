-- Prove2me | solution 1 for RamanujanNotebooks.entry_31_24
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:29:47.901089+00:00
-- url     : https://prove2.me/submissions/718d86d4-6507-4f06-86d5-27c6eed99d69

import Mathlib

namespace RNE31
open Real Filter Topology

section
variable (x : ℝ) (hx0 : x ≠ 0)
  (hx : ∀ k : ℕ, 1 ≤ k → ∀ j : ℤ, x / 2 ^ k ≠ (2 * (j : ℝ) + 1) * (Real.pi / 2))
include hx0 hx

lemma sin_ne (k : ℕ) : sin (x / 2 ^ k) ≠ 0 := by
  intro h
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp h
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
    exact hx0 (by
      have : x / 2 ^ k = 0 := hm.symm
      rcases div_eq_zero_iff.mp this with h | h
      · exact h
      · exact absurd h (by positivity))
  obtain ⟨e, o, ho, he⟩ := Nat.exists_eq_two_pow_mul_odd (Int.natAbs_ne_zero.mpr hm0)
  obtain ⟨j, hj⟩ := ho
  -- m = ± 2^e * o
  have hmo : (m : ℝ) = 2 ^ e * (if 0 ≤ m then (o : ℝ) else -(o : ℝ)) := by
    rcases le_or_gt 0 m with hpos | hneg
    · rw [if_pos hpos]
      have : m = (m.natAbs : ℤ) := (Int.natAbs_of_nonneg hpos).symm
      rw [this, he]; push_cast; ring
    · rw [if_neg (not_le.mpr hneg)]
      have : m = -(m.natAbs : ℤ) := by omega
      rw [this, he]; push_cast; ring
  apply hx (k + e + 1) (by omega) (if 0 ≤ m then (j : ℤ) else -(j : ℤ) - 1)
  have hx' : x = 2 ^ k * (m * π) := by
    field_simp at hm; linarith
  rw [hx', hmo, hj]
  split_ifs <;> push_cast <;> field_simp <;> ring

lemma cos_ne (k : ℕ) (hk : 1 ≤ k) : cos (x / 2 ^ k) ≠ 0 := by
  intro h
  obtain ⟨j, hj⟩ := Real.cos_eq_zero_iff.mp h
  exact hx k hk j (by rw [hj]; ring)

lemma term_eq (k : ℕ) : tan (x / 2 ^ (k + 1)) / 2 ^ (k + 1) =
    cos (x / 2 ^ (k + 1)) / sin (x / 2 ^ (k + 1)) / 2 ^ (k + 1) -
      cos (x / 2 ^ k) / sin (x / 2 ^ k) / 2 ^ k := by
  have hs := sin_ne x hx0 hx (k + 1)
  have hc := cos_ne x hx0 hx (k + 1) (by omega)
  have hs2 := sin_ne x hx0 hx k
  set y := x / 2 ^ (k + 1) with hy
  have h2 : x / 2 ^ k = 2 * y := by rw [hy, pow_succ]; field_simp
  rw [h2] at hs2 ⊢
  rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul, Real.cos_two_mul]
  rw [Real.sin_two_mul] at hs2
  have hsq := Real.sin_sq_add_cos_sq y
  field_simp
  rw [pow_succ]
  field_simp
  linear_combination (2 * (2 : ℝ) ^ k) * hsq

theorem main :
    HasSum (fun k : ℕ => Real.tan (x / 2 ^ (k + 1)) / 2 ^ (k + 1))
      (1 / x - Real.cos x / Real.sin x) := by
  set f : ℕ → ℝ := fun k => cos (x / 2 ^ k) / sin (x / 2 ^ k) / 2 ^ k with hf
  have hterm : ∀ k, tan (x / 2 ^ (k + 1)) / 2 ^ (k + 1) = f (k + 1) - f k :=
    fun k => term_eq x hx0 hx k
  -- summability
  have htan : Tendsto (fun k : ℕ => tan (x / 2 ^ (k + 1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => x / 2 ^ (k + 1)) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
        (tendsto_add_atTop_nat 1)
      exact tendsto_const_nhds.div_atTop this
    have h2 : ContinuousAt tan 0 := Real.continuousAt_tan.mpr (by simp)
    simpa [Function.comp_def] using h2.tendsto.comp h1
  have hsum : Summable (fun k : ℕ => tan (x / 2 ^ (k + 1)) / 2 ^ (k + 1)) := by
    apply Summable.of_norm_bounded_eventually_nat (g := fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1))
    · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
        (add_left_injective 1)
    · filter_upwards [(htan.eventually (Metric.ball_mem_nhds 0 one_pos))] with k hk
      rw [Real.dist_eq, sub_zero] at hk
      rw [Real.norm_eq_abs, abs_div, abs_pow, abs_two, div_eq_mul_inv, one_div, inv_pow]
      exact mul_le_of_le_one_left (by positivity) hk.le
  rw [hsum.hasSum_iff_tendsto_nat]
  simp_rw [hterm, Finset.sum_range_sub (fun k => f k)]
  have hf0 : f 0 = cos x / sin x := by simp [hf]
  rw [hf0]
  refine Tendsto.sub_const ?_ _
  -- f K → 1/x
  have hy : Tendsto (fun K : ℕ => x / 2 ^ K) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hlim : Tendsto (fun K : ℕ => cos (x / 2 ^ K) / (sinc (x / 2 ^ K) * x)) atTop
      (𝓝 (1 / x)) := by
    have hc : Tendsto (fun K : ℕ => cos (x / 2 ^ K)) atTop (𝓝 1) := by
      simpa [Function.comp_def] using (Real.continuous_cos.tendsto 0).comp hy
    have hs : Tendsto (fun K : ℕ => sinc (x / 2 ^ K)) atTop (𝓝 1) := by
      simpa [Function.comp_def, sinc_zero] using (Real.continuous_sinc.tendsto 0).comp hy
    have := hc.div (hs.mul_const x) (by simpa using hx0)
    simpa [Pi.div_def] using this
  refine hlim.congr (fun K => ?_)
  have hyne : x / 2 ^ K ≠ 0 := div_ne_zero hx0 (by positivity)
  rw [hf]
  simp only
  rw [sinc, if_neg hyne]
  have hs := sin_ne x hx0 hx K
  field_simp

end

end RNE31

theorem solution (x : ℝ) (hx0 : x ≠ 0)
    (hx : ∀ k : ℕ, 1 ≤ k → ∀ j : ℤ, x / 2 ^ k ≠ (2 * (j : ℝ) + 1) * (Real.pi / 2)) :
    HasSum (fun k : ℕ => Real.tan (x / 2 ^ (k + 1)) / 2 ^ (k + 1))
      (1 / x - Real.cos x / Real.sin x) :=
  RNE31.main x hx0 hx
