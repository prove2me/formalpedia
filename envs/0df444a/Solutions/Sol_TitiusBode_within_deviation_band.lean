-- Prove2me | solution 1 for TitiusBode.within_deviation_band
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T19:32:34.239678+00:00
-- url     : https://prove2.me/submissions/c93e04e3-a14b-49ef-b25b-6ff866b2b576

import Definitions.Def_TitiusBode_Defs
import Mathlib
open Filter Topology
open TitiusBode

theorem doubling_covering_aux (p : ℕ → ℝ) (hstep : ∀ k, p (k + 1) ≤ 2 * p k)
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

theorem solution (d : ℝ) (hd : 0.3 ≤ d) :
    ∃ n : WithBot ℕ, -0.25 ≤ deviation d (tbAU n) ∧ deviation d (tbAU n) ≤ 0.5 := by
  -- the predicted positions, listed as a sequence indexed by ℕ: `-∞, 0, 1, 2, …`
  let p : ℕ → ℝ := fun k => Nat.casesOn k (tbAU ⊥) (fun m => tbAU (m : WithBot ℕ))
  have hp0 : p 0 = 0.4 := by simp [p, tbAU, twoPowExt]
  have hps : ∀ m : ℕ, p (m + 1) = 0.4 + 0.3 * 2 ^ m := by
    intro m; simp [p, tbAU, twoPowExt]
  have hstep : ∀ k, p (k + 1) ≤ 2 * p k := by
    intro k
    cases k with
    | zero => rw [hps, hp0]; norm_num
    | succ m => rw [hps, hps, pow_succ]; nlinarith [pow_pos (two_pos : (0:ℝ) < 2) m]
  have hunbdd : ∀ M : ℝ, ∃ k, M ≤ p k := by
    intro M
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (M / 0.3) (by norm_num : (1:ℝ) < 2)
    refine ⟨m + 1, ?_⟩
    rw [hps]
    have : M < 0.3 * 2 ^ m := by
      have := (div_lt_iff₀' (by norm_num : (0:ℝ) < 0.3)).1 hm
      linarith
    linarith
  obtain ⟨k, hk1, hk2⟩ := doubling_covering_aux p hstep hunbdd d (by rw [hp0]; linarith)
  cases k with
  | zero => exact ⟨⊥, by norm_num at hk1 ⊢; exact hk1, by norm_num at hk2 ⊢; exact hk2⟩
  | succ m => exact ⟨(m : WithBot ℕ), by norm_num at hk1 ⊢; exact hk1,
      by norm_num at hk2 ⊢; exact hk2⟩
