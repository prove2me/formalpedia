-- Prove2me | solution 1 for YeIPA.WorstCase.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:34:22.075461+00:00
-- url     : https://prove2.me/submissions/59282198-f3f3-4894-9205-7c4ea0f3a761

import Mathlib
import Definitions.Def_YeIPA_WorstCase_RankOneUpdate
open YeIPA.WorstCase

theorem g70ye_sc_pos {n : ℕ} (x : ℕ → Fin n → ℝ) (hx : ∀ t j, 0 < x t j) :
    ∀ t j, 0 < scaling x t j := by
  intro t
  induction t with
  | zero => intro j; simp only [scaling]; exact hx 0 j
  | succ k ih =>
    intro j; simp only [scaling]
    split_ifs
    · exact ih j
    · exact hx _ j

theorem g70ye_sc_succ {n : ℕ} (x : ℕ → Fin n → ℝ) (k : ℕ) (i : Fin n) :
    scaling x (k + 1) i = if i ∈ updateSet x (k + 1) then x (k + 1) i else scaling x k i := by
  simp only [scaling, updateSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Nat.add_sub_cancel]
  split_ifs <;> tauto

theorem g70ye_inv {n : ℕ} (x : ℕ → Fin n → ℝ) (hx : ∀ t j, 0 < x t j) (i : Fin n) :
    ∀ k : ℕ, (∑ t ∈ Finset.Icc 1 k, (if i ∈ updateSet x t then (1 : ℝ) else 0)) +
      11 * (|x k i - scaling x k i| / scaling x k i) ≤
      11 * ∑ t ∈ Finset.Icc 1 k, |(x t i - x (t - 1) i) / scaling x (t - 1) i| := by
  intro k
  induction k with
  | zero => simp [scaling]
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
      Nat.add_sub_cancel]
    have hd := g70ye_sc_pos x hx k i
    have hxk := hx k i
    have hxk1 := hx (k + 1) i
    set d := scaling x k i
    have hΔ : |x (k + 1) i - d| / d ≤ |x k i - d| / d + |(x (k + 1) i - x k i) / d| := by
      rw [abs_div, abs_of_pos hd, ← add_div]
      apply div_le_div_of_nonneg_right _ hd.le
      calc |x (k + 1) i - d| = |(x k i - d) + (x (k + 1) i - x k i)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    rw [g70ye_sc_succ x k i]
    by_cases hI : i ∈ updateSet x (k + 1)
    · rw [if_pos hI, if_pos hI, sub_self, abs_zero, zero_div, mul_zero, add_zero]
      have hmem := hI
      simp only [updateSet, Finset.mem_filter, Finset.mem_univ, true_and,
        Nat.add_sub_cancel] at hmem
      have hbig : 1 / 11 ≤ |x (k + 1) i - d| / d := by
        rw [le_div_iff₀ hd]
        by_cases h1 : 1 / 1.1 ≤ d / x (k + 1) i
        · have h2 : ¬ d / x (k + 1) i ≤ 1.1 := fun h2 => hmem ⟨h1, h2⟩
          push_neg at h2
          rw [lt_div_iff₀ hxk1] at h2
          rw [abs_of_neg (by nlinarith)]; nlinarith
        · push_neg at h1
          rw [div_lt_iff₀ hxk1] at h1
          rw [abs_of_pos (by nlinarith)]; nlinarith
      linarith
    · rw [if_neg hI, if_neg hI, add_zero]
      linarith


/-- Lemma 5.1 (Ye 1997, p. 149). Let `x⁰, x¹, … ∈ ℝⁿ` be positive, `dᵗ` the rank-one updating
scaling of p. 148 and `Iᵗ` its update sets. Then `‖(Dᵗ)⁻¹(xᵗ − dᵗ)‖_∞ ≤ 0.1` for every
`t = 0, 1, …`, and for every `k`,
`∑_{t=1}^k |Iᵗ| ≤ 11√n ∑_{t=1}^k ‖(Dᵗ⁻¹)⁻¹(xᵗ − xᵗ⁻¹)‖` (Euclidean norm). -/
theorem solution {n : ℕ} (x : ℕ → Fin n → ℝ) (hx : ∀ t j, 0 < x t j) :
    (∀ t : ℕ, normInf (fun j => (x t j - scaling x t j) / scaling x t j) ≤ 0.1) ∧
    ∀ k : ℕ, (∑ t ∈ Finset.Icc 1 k, ((updateSet x t).card : ℝ)) ≤
      11 * Real.sqrt n *
        ∑ t ∈ Finset.Icc 1 k, norm2 (fun j => (x t j - x (t - 1) j) / scaling x (t - 1) j) := by
  refine ⟨fun t => ?_, fun k => ?_⟩
  · apply Real.iSup_le _ (by norm_num)
    intro j
    cases t with
    | zero => simp [scaling]; norm_num
    | succ t =>
      have hd := g70ye_sc_pos x hx t j
      have hx1 := hx (t + 1) j
      simp only [scaling]
      split_ifs with h
      · obtain ⟨h1, h2⟩ := h
        rw [le_div_iff₀ hx1] at h1
        rw [div_le_iff₀ hx1] at h2
        rw [abs_div, abs_of_pos hd, div_le_iff₀ hd, abs_le]
        constructor <;> nlinarith
      · norm_num
  · have hcard : ∀ t, ((updateSet x t).card : ℝ) =
        ∑ i, (if i ∈ updateSet x t then (1 : ℝ) else 0) := by
      intro t
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
    simp only [hcard]
    rw [Finset.sum_comm]
    have h1 : ∀ i, (∑ t ∈ Finset.Icc 1 k, (if i ∈ updateSet x t then (1 : ℝ) else 0)) ≤
        11 * ∑ t ∈ Finset.Icc 1 k, |(x t i - x (t - 1) i) / scaling x (t - 1) i| := by
      intro i
      have := g70ye_inv x hx i k
      have : 0 ≤ 11 * (|x k i - scaling x k i| / scaling x k i) :=
        mul_nonneg (by norm_num) (div_nonneg (abs_nonneg _) (g70ye_sc_pos x hx k i).le)
      linarith
    have hcs : ∀ t, ∑ i, |(x t i - x (t - 1) i) / scaling x (t - 1) i| ≤
        Real.sqrt n * norm2 (fun j => (x t j - x (t - 1) j) / scaling x (t - 1) j) := by
      intro t
      set v : Fin n → ℝ := fun j => (x t j - x (t - 1) j) / scaling x (t - 1) j
      have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun j => |v j|)
      simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, sq_abs] at hc
      unfold norm2
      rw [← Real.sqrt_mul (Nat.cast_nonneg n)]
      calc ∑ i, |v i| = Real.sqrt ((∑ i, |v i|) ^ 2) :=
            (Real.sqrt_sq (Finset.sum_nonneg fun i _ => abs_nonneg _)).symm
        _ ≤ _ := Real.sqrt_le_sqrt hc
    calc ∑ i, ∑ t ∈ Finset.Icc 1 k, (if i ∈ updateSet x t then (1 : ℝ) else 0)
        ≤ ∑ i, 11 * ∑ t ∈ Finset.Icc 1 k, |(x t i - x (t - 1) i) / scaling x (t - 1) i| :=
          Finset.sum_le_sum fun i _ => h1 i
      _ = 11 * ∑ t ∈ Finset.Icc 1 k, ∑ i, |(x t i - x (t - 1) i) / scaling x (t - 1) i| := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ 11 * ∑ t ∈ Finset.Icc 1 k,
            Real.sqrt n * norm2 (fun j => (x t j - x (t - 1) j) / scaling x (t - 1) j) := by
          gcongr with t _; exact hcs t
      _ = _ := by rw [← Finset.mul_sum]; ring



