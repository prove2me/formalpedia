-- Prove2me | solution 1 for TitiusBode.doubling_covering
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T19:32:33.822438+00:00
-- url     : https://prove2.me/submissions/a639068f-2336-458a-8822-1423ec71d29f

import Definitions.Def_TitiusBode_Defs
import Mathlib
open Filter Topology
open TitiusBode

theorem solution (p : ℕ → ℝ) (hstep : ∀ k, p (k + 1) ≤ 2 * p k)
    (hunbdd : ∀ M : ℝ, ∃ k, M ≤ p k) (d : ℝ) (hd : 3 / 4 * p 0 ≤ d) :
    ∃ k, -1 / 4 ≤ deviation d (p k) ∧ deviation d (p k) ≤ 1 / 2 := by
  -- every term is positive: a nonpositive term would force all later terms to be nonpositive
  have hpos : ∀ k, 0 < p k := by
    intro k
    by_contra hk
    push_neg at hk
    have hle : ∀ j, p (k + j) ≤ 0 := by
      intro j
      induction j with
      | zero => simpa using hk
      | succ j ih =>
        have := hstep (k + j)
        rw [← add_assoc]; linarith
    have hgeom : ∀ i, p i ≤ 2 ^ i * p 0 := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ]; nlinarith [hstep i]
    have hlow : ∀ j, j ≤ k → p j ≤ 2 ^ k * |p 0| := by
      intro j hj
      have h1 := hgeom j
      have h2 : (2:ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hj
      have h3 : 2 ^ j * p 0 ≤ 2 ^ j * |p 0| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      have h4 : 2 ^ j * |p 0| ≤ 2 ^ k * |p 0| :=
        mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
      linarith
    obtain ⟨m, hm⟩ := hunbdd (2 ^ k * |p 0| + 1)
    rcases le_or_gt m k with hmk | hmk
    · have := hlow m hmk
      linarith
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hmk
      have := hle (j + 1)
      rw [← add_assoc] at this
      nlinarith [pow_pos (two_pos : (0:ℝ) < 2) k, abs_nonneg (p 0)]
  have hex : ∃ k, 2 / 3 * d ≤ p k := hunbdd _
  classical
  let k := Nat.find hex
  have hk : 2 / 3 * d ≤ p k := Nat.find_spec hex
  have hupper : p k ≤ 4 / 3 * d := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos'
    · rw [h0]; linarith
    · obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hlt : j < k := by omega
      have hmin : ¬ (2 / 3 * d ≤ p j) := Nat.find_min hex hlt
      push_neg at hmin
      have := hstep j
      rw [← hj] at this
      linarith
  refine ⟨k, ?_, ?_⟩
  · unfold deviation
    rw [le_div_iff₀ (hpos k)]
    linarith
  · unfold deviation
    rw [div_le_iff₀ (hpos k)]
    linarith
