-- Prove2me | solution 1 for RecMarkovGraph.IndepLB.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-27T18:14:22.681376+00:00
-- url     : https://prove2.me/submissions/d6043daa-f4ef-46af-b178-73d809fcd82f

import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB

open Finset

theorem rs_pos_lt (a x : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hx : 0 < x) (hx1 : x < 1) :
    ∀ k, 0 < recSeq a x k ∧ recSeq a x k < 1 := by
  intro k
  induction k with
  | zero => exact ⟨hx, hx1⟩
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    simp only [recSeq, fa]
    have h2 : a * recSeq a x k < 1 := by nlinarith
    constructor
    · exact mul_pos h0 (by linarith)
    · nlinarith [mul_pos ha h0]

theorem rs_scale (a x : ℝ) : ∀ k, a * recSeq a x k = recSeq 1 (a * x) k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp only [recSeq, fa]; rw [← ih]; ring

theorem rs_inv_lower (a x : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hx : 0 < x) (hx1 : x < 1) :
    ∀ k : ℕ, 1 / x + a * ((k : ℝ) + 1) < 1 / recSeq a x (k + 1) := by
  have step : ∀ k, 1 / recSeq a x k + a < 1 / recSeq a x (k + 1) := by
    intro k
    obtain ⟨h0, h1⟩ := rs_pos_lt a x ha ha1 hx hx1 k
    set y := recSeq a x k
    have hay : a * y < 1 := by nlinarith
    show 1 / y + a < 1 / (y * (1 - a * y))
    have hp : 0 < y * (1 - a * y) := mul_pos h0 (by linarith)
    rw [div_add' _ _ _ h0.ne', div_lt_div_iff₀ h0 hp]
    nlinarith [mul_pos (mul_pos ha ha) (mul_pos h0 h0), mul_pos h0 h0]
  intro k
  induction k with
  | zero => simpa [recSeq] using step 0
  | succ k ih =>
    have := step (k + 1)
    push_cast
    linarith

/-- `S k = ∑_{j<k} 1/(j+3)` is at most `1/3 + √(k+2)` and at most `k/3`. -/
theorem harm_bound : ∀ k : ℕ, ∑ j ∈ range k, (1 : ℝ) / ((j : ℝ) + 3) ≤ 1 / 3 + Real.sqrt ((k : ℝ) + 2) := by
  intro k
  induction k with
  | zero => simp; positivity
  | succ k ih =>
    rw [sum_range_succ]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have key : (1 : ℝ) / ((k : ℝ) + 3) ≤ Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2) := by
        have s3 := Real.sq_sqrt (show (0 : ℝ) ≤ (k : ℝ) + 3 by positivity)
        have s2 := Real.sq_sqrt (show (0 : ℝ) ≤ (k : ℝ) + 2 by positivity)
        have p3 : 0 ≤ Real.sqrt ((k : ℝ) + 3) := Real.sqrt_nonneg _
        have p2 : 0 ≤ Real.sqrt ((k : ℝ) + 2) := Real.sqrt_nonneg _
        have h23 : Real.sqrt ((k : ℝ) + 2) ≤ Real.sqrt ((k : ℝ) + 3) :=
          Real.sqrt_le_sqrt (by linarith)
        have h2le : 2 ≤ Real.sqrt ((k : ℝ) + 3) := by
          rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith
        have hprod : (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
            (Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2)) = 1 := by
          nlinarith [s3, s2]
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      have : ((k + 1 : ℕ) : ℝ) + 2 = (k : ℝ) + 3 := by push_cast; ring
      rw [this]
      linarith

theorem harm_bound' : ∀ k : ℕ, ∑ j ∈ range k, (1 : ℝ) / ((j : ℝ) + 3) ≤ (k : ℝ) / 3 := by
  intro k
  calc ∑ j ∈ range k, (1 : ℝ) / ((j : ℝ) + 3) ≤ ∑ j ∈ range k, (1 : ℝ) / 3 := by
        apply sum_le_sum; intro j _
        apply one_div_le_one_div_of_le (by norm_num); linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    _ = (k : ℝ) / 3 := by simp; ring

/-- Reciprocal bounds for the iterates of `f₁` started at `y ∈ (0,1)`. -/
theorem w_bounds (y : ℝ) (hy : 0 < y) (hy1 : y < 1) :
    ∀ k : ℕ, 1 / fa 1 y + k ≤ 1 / recSeq 1 y (k + 1) ∧
      1 / recSeq 1 y (k + 1) ≤ 1 / fa 1 y + k + ∑ j ∈ range k, (1 : ℝ) / ((j : ℝ) + 3) := by
  have hz4 : 4 ≤ 1 / fa 1 y := by
    have hz : 0 < fa 1 y := by simp only [fa]; nlinarith
    rw [le_div_iff₀ hz]; simp only [fa]; nlinarith [sq_nonneg (2 * y - 1)]
  intro k
  induction k with
  | zero => simp [recSeq]
  | succ k ih =>
    obtain ⟨hl, hu⟩ := ih
    obtain ⟨h0, h1⟩ := rs_pos_lt 1 y one_pos le_rfl hy hy1 (k + 1)
    set Y := recSeq 1 y (k + 1) with hY
    have hrec : recSeq 1 y (k + 1 + 1) = Y * (1 - Y) := by
      show fa 1 Y = _; simp [fa]
    have hid : 1 / (Y * (1 - Y)) = 1 / Y + 1 + Y / (1 - Y) := by
      field_simp [h0.ne', (show (1 : ℝ) - Y ≠ 0 by linarith)]
      ring
    rw [hrec, hid, sum_range_succ]
    have hYq : 0 ≤ Y / (1 - Y) := div_nonneg h0.le (by linarith)
    have hYle : Y ≤ 1 / ((k : ℝ) + 4) := by
      have : (k : ℝ) + 4 ≤ 1 / Y := by linarith
      rw [le_div_iff₀ h0] at this
      rw [le_div_iff₀ (by positivity)]; linarith
    have hYk : Y / (1 - Y) ≤ 1 / ((k : ℝ) + 3) := by
      have hk4 : (0 : ℝ) < (k : ℝ) + 4 := by positivity
      rw [div_le_div_iff₀ (by linarith) (by positivity)]
      rw [le_div_iff₀ hk4] at hYle
      nlinarith
    push_cast
    constructor <;> linarith

theorem lemma_4_2 (a x₁ : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hx₁ : 0 < x₁) (hx₁1 : x₁ < 1) :
    (∀ k : ℕ, recSeq a x₁ (k + 1) < recSeq a x₁ k) ∧
    ∀ n : ℕ, 2 ≤ n →
      ell n (a * x₁) / a ≤ recSeq a x₁ (n - 1) ∧
      recSeq a x₁ (n - 1) ≤ 1 / (4 * a) ∧
      recSeq a x₁ (n - 1) < 1 / a * (1 / ((n : ℝ) - 1 + 1 / x₁)) := by
  have hpos := rs_pos_lt a x₁ ha ha1 hx₁ hx₁1
  refine ⟨?_, ?_⟩
  · intro k
    obtain ⟨h0, h1⟩ := hpos k
    show recSeq a x₁ k * (1 - a * recSeq a x₁ k) < recSeq a x₁ k
    nlinarith [mul_pos ha (mul_pos h0 h0)]
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hn1 : m + 2 - 1 = m + 1 := by omega
  rw [hn1]
  obtain ⟨h0, h1⟩ := hpos (m + 1)
  refine ⟨?_, ?_, ?_⟩
  · -- lower bound via the iterates of f₁
    set y := a * x₁ with hy
    have hy0 : 0 < y := mul_pos ha hx₁
    have hy1 : y < 1 := by nlinarith
    have hsc := rs_scale a x₁ (m + 1)
    rw [div_le_iff₀ ha, mul_comm, hsc]
    obtain ⟨hl, hu⟩ := w_bounds y hy0 hy1 m
    obtain ⟨Y0, Y1⟩ := rs_pos_lt 1 y one_pos le_rfl hy0 hy1 (m + 1)
    set Y := recSeq 1 y (m + 1)
    have hz : 0 < fa 1 y := by simp only [fa]; nlinarith
    have hz4 : 4 ≤ 1 / fa 1 y := by
      rw [le_div_iff₀ hz]; simp only [fa]; nlinarith [sq_nonneg (2 * y - 1)]
    have hcast : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
    unfold ell
    rw [hcast]
    split_ifs with hc
    · have hsq : 1 / fa 1 y - 1 ≤ Real.sqrt ((m : ℝ) + 2) :=
        (Real.le_sqrt (by linarith) (by positivity)).mpr hc
      have hS := harm_bound m
      have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ (m : ℝ) + 2 by positivity)
      have hsn := Real.sqrt_nonneg ((m : ℝ) + 2)
      rw [div_le_iff₀ (by positivity)]
      have hYinv : 1 / Y ≤ (Real.sqrt ((m : ℝ) + 2) + 1) ^ 2 := by nlinarith
      rw [div_le_iff₀ Y0] at hYinv
      linarith
    · have hS := harm_bound' m
      have hYinv : 1 / Y ≤ ((m : ℝ) + 2) * (1 / fa 1 y) := by
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        nlinarith
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ Y0] at hYinv
      have : fa 1 y * (1 / fa 1 y) = 1 := by field_simp
      nlinarith
  · -- upper bound 1/(4a)
    show recSeq a x₁ m * (1 - a * recSeq a x₁ m) ≤ 1 / (4 * a)
    rw [le_div_iff₀ (by linarith)]
    nlinarith [sq_nonneg (2 * a * recSeq a x₁ m - 1)]
  · have hl := rs_inv_lower a x₁ ha ha1 hx₁ hx₁1 m
    have hcast : ((m + 2 : ℕ) : ℝ) - 1 = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hx1inv : a * (1 / x₁) ≤ 1 / x₁ := by
      have : 0 < 1 / x₁ := by positivity
      nlinarith
    have hD : 0 < (m : ℝ) + 1 + 1 / x₁ := by positivity
    rw [one_div_mul_one_div, lt_div_iff₀ (by positivity)]
    rw [lt_div_iff₀ h0] at hl
    nlinarith


-- Platform entry point: restates the target verbatim.
namespace RecMarkovGraph.IndepLB

theorem _root_.solution (a x₁ : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hx₁ : 0 < x₁) (hx₁1 : x₁ < 1) :
    (∀ k : ℕ, recSeq a x₁ (k + 1) < recSeq a x₁ k) ∧
    ∀ n : ℕ, 2 ≤ n →
      ell n (a * x₁) / a ≤ recSeq a x₁ (n - 1) ∧
      recSeq a x₁ (n - 1) ≤ 1 / (4 * a) ∧
      recSeq a x₁ (n - 1) < 1 / a * (1 / ((n : ℝ) - 1 + 1 / x₁)) := by
  apply @RecMarkovGraph.IndepLB.lemma_4_2 <;> assumption

end RecMarkovGraph.IndepLB
