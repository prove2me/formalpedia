-- Prove2me | solution 1 for RobustOdds.SVM.advMarginLoss_eq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:20:06.212185+00:00
-- url     : https://prove2.me/submissions/44ebd70c-8648-49e9-a0a0-8584bb627479

import Mathlib
import Definitions.Def_RobustOdds_SVM_Setting

set_option autoImplicit false

open MeasureTheory RobustOdds.SVM

lemma ams_pointwise (d : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (w x : Fin (d + 1) → ℝ) (y : ℝ)
    (hy : y = 1 ∨ y = -1) :
    advHingeLoss ε w x y = max 0 (1 - y * ∑ i, w i * x i + ε * ∑ i, |w i|) := by
  unfold advHingeLoss hingeLoss
  have hy2 : y * y = 1 := by rcases hy with rfl | rfl <;> norm_num
  have hyabs : |y| = 1 := by rcases hy with rfl | rfl <;> simp
  have hsplit : ∀ δ : Fin (d + 1) → ℝ, ∑ i, w i * (x + δ) i = ∑ i, w i * x i + ∑ i, w i * δ i := by
    intro δ
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hub : ∀ δ : {δ : Fin (d + 1) → ℝ // ‖δ‖ ≤ ε},
      max 0 (1 - y * ∑ i, w i * (x + δ.val) i) ≤
        max 0 (1 - y * ∑ i, w i * x i + ε * ∑ i, |w i|) := by
    intro δ
    refine max_le_max le_rfl ?_
    have hδi : ∀ i, |δ.val i| ≤ ε := fun i => by
      have := norm_le_pi_norm δ.val i
      rw [Real.norm_eq_abs] at this
      exact this.trans δ.2
    have h1 : -(y * ∑ i, w i * δ.val i) ≤ ε * ∑ i, |w i| := by
      calc -(y * ∑ i, w i * δ.val i) = ∑ i, -(y * (w i * δ.val i)) := by
            rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        _ ≤ ∑ i, ε * |w i| := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            calc -(y * (w i * δ.val i)) ≤ |y * (w i * δ.val i)| := neg_le_abs _
              _ = |w i| * |δ.val i| := by rw [abs_mul, abs_mul, hyabs, one_mul]
              _ ≤ |w i| * ε := mul_le_mul_of_nonneg_left (hδi i) (abs_nonneg _)
              _ = ε * |w i| := mul_comm _ _
        _ = ε * ∑ i, |w i| := by rw [Finset.mul_sum]
    rw [hsplit]
    nlinarith [h1]
  set δs : Fin (d + 1) → ℝ := fun i => -(ε * y) * (if 0 ≤ w i then 1 else -1) with hδs
  have hδsn : ‖δs‖ ≤ ε := by
    rw [pi_norm_le_iff_of_nonneg hε]
    intro i
    rw [Real.norm_eq_abs, hδs]
    simp only [abs_mul, abs_neg, hyabs, abs_of_nonneg hε]
    split_ifs <;> simp
  have hws : ∀ i, w i * δs i = -(ε * y) * |w i| := by
    intro i
    simp only [hδs]
    by_cases h : 0 ≤ w i
    · simp [h, abs_of_nonneg h]; ring
    · have h' : w i < 0 := not_le.1 h
      simp [h, abs_of_neg h']; ring
  have hattain : max 0 (1 - y * ∑ i, w i * (x + δs) i) =
      max 0 (1 - y * ∑ i, w i * x i + ε * ∑ i, |w i|) := by
    congr 1
    rw [hsplit]
    simp only [hws, ← Finset.mul_sum]
    linear_combination (ε * ∑ i, |w i|) * hy2
  haveI : Nonempty {δ : Fin (d + 1) → ℝ // ‖δ‖ ≤ ε} := ⟨⟨δs, hδsn⟩⟩
  refine le_antisymm (ciSup_le hub) ?_
  have hbdd : BddAbove (Set.range fun δ : {δ : Fin (d + 1) → ℝ // ‖δ‖ ≤ ε} =>
      max 0 (1 - y * ∑ i, w i * (x + δ.val) i)) :=
    ⟨_, Set.forall_mem_range.2 hub⟩
  calc max 0 (1 - y * ∑ i, w i * x i + ε * ∑ i, |w i|)
      = max 0 (1 - y * ∑ i, w i * (x + δs) i) := hattain.symm
    _ ≤ _ := le_ciSup hbdd (⟨δs, hδsn⟩ : {δ : Fin (d + 1) → ℝ // ‖δ‖ ≤ ε})

theorem solution (d : ℕ) (p η ε : ℝ) (hε : 0 ≤ ε)
    (w : Fin (d + 1) → ℝ) :
    advMarginLoss d p η ε w =
      (1 / 2) * ∫ x, max 0 (1 - ∑ i, w i * x i + ε * ∑ i, |w i|)
        ∂(RobustOdds.Tradeoff.condLaw d p η 1) +
      (1 / 2) * ∫ x, max 0 (1 + ∑ i, w i * x i + ε * ∑ i, |w i|)
        ∂(RobustOdds.Tradeoff.condLaw d p η (-1)) := by
  unfold advMarginLoss
  have e1 : (fun x : Fin (d + 1) → ℝ => advHingeLoss ε w x 1) =
      fun x => max 0 (1 - ∑ i, w i * x i + ε * ∑ i, |w i|) := by
    funext x
    rw [ams_pointwise d ε hε w x 1 (Or.inl rfl)]
    congr 1; ring
  have e2 : (fun x : Fin (d + 1) → ℝ => advHingeLoss ε w x (-1)) =
      fun x => max 0 (1 + ∑ i, w i * x i + ε * ∑ i, |w i|) := by
    funext x
    rw [ams_pointwise d ε hε w x (-1) (Or.inr rfl)]
    congr 1; ring
  rw [e1, e2]
