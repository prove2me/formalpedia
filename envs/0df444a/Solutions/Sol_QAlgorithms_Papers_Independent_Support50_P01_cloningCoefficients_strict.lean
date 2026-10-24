-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P01.cloningCoefficients_strict
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:01:29.514453+00:00
-- url     : https://prove2.me/submissions/6dc3e9c7-7ef3-49f8-ad7f-315e943ba300

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P01

namespace QAlgorithms.Papers.Independent.Support50.P01

theorem x5cl_zero (N M j : ℕ) (h : M - N < j) : cloningAlpha N M j = 0 := by
  simp [cloningAlpha, not_le.mpr h]

theorem x5cl_pos (N M j : ℕ) (h : j ≤ M - N) : 0 < cloningAlpha N M j := by
  rw [cloningAlpha, if_pos h]; positivity

theorem x5cl_nonneg (N M j : ℕ) : 0 ≤ cloningAlpha N M j := by
  by_cases h : j ≤ M - N
  · exact (x5cl_pos N M j h).le
  · rw [x5cl_zero N M j (by omega)]

theorem x5cl_a0 (N M : ℕ) : cloningAlpha N M 0 = (N + 1) / (M + 1) := by
  rw [cloningAlpha, if_pos (Nat.zero_le _)]
  simp only [Nat.sub_zero]
  have h1 : (Nat.factorial (M - N) : ℝ) ≠ 0 := by positivity
  have h2 : (Nat.factorial M : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem x5cl_rec (N M j : ℕ) (hNM : N ≤ M) :
    cloningAlpha N M (j + 1) * ((M - j : ℕ) : ℝ) =
      cloningAlpha N M j * ((M - N - j : ℕ) : ℝ) := by
  by_cases hj : j < M - N
  · obtain ⟨D, rfl⟩ : ∃ D, M = N + D := ⟨M - N, by omega⟩
    obtain ⟨a, rfl⟩ : ∃ a, D = j + 1 + a := ⟨D - j - 1, by omega⟩
    have e0 : N + (j + 1 + a) - N = j + 1 + a := by omega
    have e1 : N + (j + 1 + a) - j = (N + a) + 1 := by omega
    have e2 : N + (j + 1 + a) - (j + 1) = N + a := by omega
    have e3 : j + 1 + a - j = a + 1 := by omega
    have e4 : j + 1 + a - (j + 1) = a := by omega
    rw [cloningAlpha, cloningAlpha, if_pos (by omega), if_pos (by omega)]
    simp only [e0, e1, e2, e3, e4, Nat.factorial_succ]
    have h1 : (Nat.factorial a : ℝ) ≠ 0 := by positivity
    have h2 : (Nat.factorial (N + (j + 1 + a)) : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  · rw [x5cl_zero N M (j + 1) (by omega)]
    have : M - N - j = 0 := by omega
    simp [this]

theorem x5cl_alpha_strict (N M j : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (hj : j < M - N) :
    cloningAlpha N M (j + 1) < cloningAlpha N M j := by
  have hr := x5cl_rec N M j hNM
  have hp := x5cl_pos N M j (by omega)
  have hlt : ((M - N - j : ℕ) : ℝ) < ((M - j : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hpos : (0 : ℝ) < ((M - j : ℕ) : ℝ) := by exact_mod_cast (by omega)
  by_contra hc
  push Not at hc
  have := mul_le_mul_of_nonneg_right hc hpos.le
  nlinarith [mul_lt_mul_of_pos_left hlt hp]

theorem x5cl_alpha_mono (N M j : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    cloningAlpha N M (j + 1) ≤ cloningAlpha N M j := by
  by_cases hj : j < M - N
  · exact (x5cl_alpha_strict N M j hN hNM hj).le
  · rw [x5cl_zero N M (j + 1) (by omega)]; exact x5cl_nonneg N M j

theorem x5cl_beta_strict (N M j : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (hj : j < M - N) :
    cloningBeta N M (j + 1) < cloningBeta N M j := by
  have hr := x5cl_rec N M j hNM
  have hp := x5cl_pos N M j (by omega)
  have hm := x5cl_alpha_mono N M (j + 1) hN hNM
  have c1 : ((M - j : ℕ) : ℝ) = (M : ℝ) - j := by
    rw [Nat.cast_sub (by omega)]
  have c2 : ((M - (j + 1) : ℕ) : ℝ) = (M : ℝ) - j - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have c3 : ((M - N - j : ℕ) : ℝ) = (M : ℝ) - N - j := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  have hM : (0 : ℝ) < M := by exact_mod_cast (by omega)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [c1, c3] at hr
  unfold cloningBeta
  rw [c1, c2, ← add_div, ← add_div, div_lt_div_iff_of_pos_right hM]
  have k1 : 0 ≤ ((j : ℝ) + 1 + 1) * (cloningAlpha N M (j + 1) - cloningAlpha N M (j + 1 + 1)) :=
    mul_nonneg (by positivity) (by linarith)
  have k2 : 0 < (N : ℝ) * cloningAlpha N M j := mul_pos (by linarith) hp
  push_cast
  nlinarith

theorem x5cl_prefix (N M : ℕ) (hNM : N ≤ M) :
    ∀ k ≤ M, (∑ j ∈ Finset.range k, cloningBeta N M j) =
      (∑ j ∈ Finset.range k, cloningAlpha N M j) + k * cloningAlpha N M k / M := by
  intro k
  induction k with
  | zero => intro; simp
  | succ k ih =>
    intro hk
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih (by omega)]
    have hM : (0 : ℝ) < M := by exact_mod_cast (by omega)
    have c1 : ((M - k : ℕ) : ℝ) = (M : ℝ) - k := by rw [Nat.cast_sub (by omega)]
    unfold cloningBeta
    rw [c1]
    field_simp
    push_cast
    ring

theorem x5cl_alpha_sum (N M : ℕ) (hNM : N ≤ M) :
    ∀ k ≤ M - N + 1, (∑ j ∈ Finset.range k, cloningAlpha N M j) =
      1 - cloningAlpha N M k * ((M : ℝ) + 1 - k) / (N + 1) := by
  intro k
  induction k with
  | zero =>
    intro; simp only [Finset.range_zero, Finset.sum_empty, x5cl_a0, Nat.cast_zero, sub_zero]
    have : (M : ℝ) + 1 ≠ 0 := by positivity
    have : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp; ring
  | succ k ih =>
    intro hk
    rw [Finset.sum_range_succ, ih (by omega)]
    have hr := x5cl_rec N M k hNM
    have c1 : ((M - k : ℕ) : ℝ) = (M : ℝ) - k := by rw [Nat.cast_sub (by omega)]
    have c3 : ((M - N - k : ℕ) : ℝ) = (M : ℝ) - N - k := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    rw [c1, c3] at hr
    have : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    push_cast
    linear_combination hr

theorem x5cl_maj (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) : CloningMajorizes N M := by
  have hz := x5cl_zero N M (M - N + 1) (by omega)
  have hsa : (∑ j ∈ Finset.range (M - N + 1), cloningAlpha N M j) = 1 := by
    rw [x5cl_alpha_sum N M hNM _ le_rfl, hz]; simp
  refine ⟨fun j _ => ⟨x5cl_nonneg N M j, ?_⟩, fun j hj =>
    ⟨(x5cl_alpha_strict N M j hN hNM hj).le, (x5cl_beta_strict N M j hN hNM hj).le⟩,
    fun k hk => ?_, hsa, ?_⟩
  · unfold cloningBeta
    have := x5cl_nonneg N M j
    have := x5cl_nonneg N M (j + 1)
    positivity
  · rw [x5cl_prefix N M hNM k (by omega)]
    have := x5cl_nonneg N M k
    have : (0 : ℝ) ≤ k * cloningAlpha N M k / M := by positivity
    linarith
  · rw [x5cl_prefix N M hNM _ (by omega), hsa, hz]; simp

end QAlgorithms.Papers.Independent.Support50.P01

open QAlgorithms.Papers.Independent.Support50.P01 in
theorem solution (N M : ℕ) (hN : 1≤N) (hNM : N≤M) :
    ∀ j : ℕ, j<M-N → cloningAlpha N M (j+1) < cloningAlpha N M j ∧
      cloningBeta N M (j+1) < cloningBeta N M j :=
  fun j hj => ⟨x5cl_alpha_strict N M j hN hNM hj, x5cl_beta_strict N M j hN hNM hj⟩
