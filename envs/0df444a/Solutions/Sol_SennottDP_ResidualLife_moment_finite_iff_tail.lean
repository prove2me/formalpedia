-- Prove2me | solution 1 for SennottDP.ResidualLife.moment_finite_iff_tail
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T14:33:04.473291+00:00
-- url     : https://prove2.me/submissions/93eb0540-a94a-4786-92a4-9be6d19dc7e9

import Mathlib
import Definitions.Def_SennottDP_ResidualLife_MSDist

open scoped ENNReal NNReal

set_option autoImplicit false

open Finset in
theorem SennottDP_RL_sum_pow_le (k w : ℕ) (hk : 1 ≤ k) :
    ∑ y ∈ range w, y ^ (k - 1) ≤ w ^ k := by
  calc ∑ y ∈ range w, y ^ (k - 1) ≤ ∑ _y ∈ range w, w ^ (k - 1) := by
        refine Finset.sum_le_sum fun y hy => ?_
        exact Nat.pow_le_pow_left (le_of_lt (Finset.mem_range.1 hy)) _
    _ = w * w ^ (k - 1) := by simp
    _ = w ^ k := by
        obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        simp [pow_succ']

open Finset in
theorem SennottDP_RL_succ_pow_le (m w : ℕ) (hw : 1 ≤ w) :
    (w + 1) ^ (m + 1) ≤ w ^ (m + 1) + 2 ^ (m + 1) * w ^ m := by
  rw [add_pow, Finset.sum_range_succ]
  simp only [one_pow, mul_one, Nat.choose_self]
  have h1 : ∑ j ∈ range (m + 1), w ^ j * (m + 1).choose j
      ≤ ∑ j ∈ range (m + 1), w ^ m * (m + 1).choose j := by
    refine Finset.sum_le_sum fun j hj => ?_
    have : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hw this)
  have h2 : ∑ j ∈ range (m + 1), (m + 1).choose j ≤ 2 ^ (m + 1) := by
    rw [← Nat.sum_range_choose]
    exact Finset.sum_le_sum_of_subset (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
  rw [← Finset.mul_sum] at h1
  have h3 : w ^ m * ∑ j ∈ range (m + 1), (m + 1).choose j ≤ w ^ m * 2 ^ (m + 1) :=
    Nat.mul_le_mul_left _ h2
  nlinarith

open Finset in
theorem SennottDP_RL_pow_le_sum (k w : ℕ) (hk : 2 ≤ k) :
    w ^ k ≤ 1 + 2 ^ k * ∑ y ∈ range w, y ^ (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction w with
  | zero => simp
  | succ w ih =>
    rw [Finset.sum_range_succ, mul_add]
    rcases Nat.eq_zero_or_pos w with h | h
    · subst h; simp
    · have := SennottDP_RL_succ_pow_le m w h
      omega

open SennottDP.ResidualLife in
theorem SennottDP_RL_tail_sum_eq (u : ℕ → ℝ≥0∞) (k : ℕ) :
    ∑' y : ℕ, (y : ℝ≥0∞) ^ (k - 1) * tail u y
      = ∑' w : ℕ, u w * ((∑ y ∈ Finset.range w, y ^ (k - 1) : ℕ) : ℝ≥0∞) := by
  unfold tail
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun w => ?_
  rw [Nat.cast_sum, Finset.mul_sum]
  rw [tsum_eq_sum (s := Finset.range w)]
  · refine Finset.sum_congr rfl fun y hy => ?_
    rw [if_pos (Finset.mem_range.1 hy)]
    push_cast
    ring
  · intro y hy
    rw [if_neg (by simpa using hy)]
    simp

open SennottDP.ResidualLife ENNReal NNReal in
theorem solution (u : ℕ → ℝ≥0∞) (hu : IsDistOnPos u) (k : ℕ) (hk : 2 ≤ k) :
    moment u k < ∞ ↔ ∑' y : ℕ, (y : ℝ≥0∞) ^ (k - 1) * tail u y < ∞ := by
  rw [SennottDP_RL_tail_sum_eq]
  unfold moment
  constructor
  · intro h
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun w => ?_) h
    rw [mul_comm]
    gcongr
    exact_mod_cast SennottDP_RL_sum_pow_le k w (by omega)
  · intro h
    have hle : ∀ w : ℕ, (w : ℝ≥0∞) ^ k * u w
        ≤ u w + 2 ^ k * (u w * ((∑ y ∈ Finset.range w, y ^ (k - 1) : ℕ) : ℝ≥0∞)) := by
      intro w
      have := SennottDP_RL_pow_le_sum k w hk
      have hc : ((w ^ k : ℕ) : ℝ≥0∞)
          ≤ ((1 + 2 ^ k * ∑ y ∈ Finset.range w, y ^ (k - 1) : ℕ) : ℝ≥0∞) := by
        exact_mod_cast this
      calc (w : ℝ≥0∞) ^ k * u w = ((w ^ k : ℕ) : ℝ≥0∞) * u w := by push_cast; ring
        _ ≤ ((1 + 2 ^ k * ∑ y ∈ Finset.range w, y ^ (k - 1) : ℕ) : ℝ≥0∞) * u w := by gcongr
        _ = u w + 2 ^ k * (u w * ((∑ y ∈ Finset.range w, y ^ (k - 1) : ℕ) : ℝ≥0∞)) := by
          push_cast; ring
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hle) ?_
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, hu.1]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top,
      ENNReal.mul_lt_top (ENNReal.pow_lt_top (by norm_num)) h⟩
