-- Prove2me | solution 1 for StochGradTrack.Const.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:29:58.921842+00:00
-- url     : https://prove2.me/submissions/eaf7ae9d-c737-41e1-915c-72148eafde9e

import Mathlib
import Definitions.Def_StochGradTrack_Const_Model

set_option autoImplicit false
open StochGradTrack.Const

theorem solution {n p : ℕ} (gradf : Fin n → E p → E p) (L : ℝ)
    (hL : ∀ i (x x' : E p), ‖gradf i x - gradf i x'‖ ≤ L * ‖x - x'‖) (x : Stack n p) :
    ‖gradAvg gradf (avg x) - hAvg gradf x‖ ≤ L / Real.sqrt n * Real.sqrt (consErr x) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [gradAvg, hAvg, consErr]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnr
  set xb := avg x with hxb
  have e : gradAvg gradf xb - hAvg gradf x = (n : ℝ)⁻¹ • ∑ i, (gradf i xb - gradf i (x i)) := by
    unfold gradAvg hAvg
    rw [Finset.sum_sub_distrib, smul_sub]
  have h1 : ‖gradAvg gradf xb - hAvg gradf x‖ ≤ (n : ℝ)⁻¹ * ∑ i, ‖gradf i xb - gradf i (x i)‖ := by
    rw [e, norm_smul, norm_inv, Real.norm_natCast]
    gcongr
    exact norm_sum_le _ _
  have h2 : ∀ i, ‖gradf i xb - gradf i (x i)‖ ≤ L * ‖x i - xb‖ := fun i => by
    have := hL i xb (x i)
    rwa [norm_sub_rev xb (x i)] at this
  set a : Fin n → ℝ := fun i => ‖x i - xb‖ with ha
  have hCS : (∑ i, a i) ≤ Real.sqrt n * Real.sqrt (consErr x) := by
    rw [← Real.sqrt_mul hnr.le]
    apply Real.le_sqrt_of_sq_le
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
    simpa [consErr, ha] using this
  rcases le_or_gt 0 L with hL0 | hL0
  · have hsq : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hnr.le).symm
    calc ‖gradAvg gradf xb - hAvg gradf x‖
        ≤ (n : ℝ)⁻¹ * ∑ i, ‖gradf i xb - gradf i (x i)‖ := h1
      _ ≤ (n : ℝ)⁻¹ * ∑ i, L * a i := by
          gcongr with i
          exact h2 i
      _ = (n : ℝ)⁻¹ * (L * ∑ i, a i) := by rw [← Finset.mul_sum]
      _ ≤ (n : ℝ)⁻¹ * (L * (Real.sqrt n * Real.sqrt (consErr x))) := by gcongr
      _ = L / Real.sqrt n * Real.sqrt (consErr x) := by
          set s := Real.sqrt n
          have hs : s ≠ 0 := hsn.ne'
          rw [hsq]
          field_simp
  · have hai : ∀ i, a i = 0 := by
      intro i
      have h := h2 i
      have h0 := norm_nonneg (gradf i xb - gradf i (x i))
      have hai0 : 0 ≤ a i := norm_nonneg _
      have : a i ≤ 0 := by
        by_contra hc
        push_neg at hc
        nlinarith [mul_pos (neg_pos.2 hL0) hc]
      linarith
    have hC : consErr x = 0 := by
      unfold consErr
      apply Finset.sum_eq_zero
      intro i _
      have := hai i
      simp only [ha] at this
      rw [this]; norm_num
    rw [hC, Real.sqrt_zero, mul_zero]
    calc ‖gradAvg gradf xb - hAvg gradf x‖
        ≤ (n : ℝ)⁻¹ * ∑ i, ‖gradf i xb - gradf i (x i)‖ := h1
      _ ≤ (n : ℝ)⁻¹ * ∑ i, L * a i := by
          gcongr with i
          exact h2 i
      _ = 0 := by simp [hai]
