-- Prove2me | solution 2 for YeIPA.LP.log_sum_bounds
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:11:42.376767+00:00
-- url     : https://prove2.me/submissions/d486f469-778c-468c-879e-be0ddca9fd96

import Mathlib
import Definitions.Def_YeIPA_LP_PotentialReduction
set_option autoImplicit false
open Matrix

theorem solution {n : ℕ} (d : Fin n → ℝ) (hd : YeIPA.LP.normInf d < 1) :
    ∑ i, Real.log (1 + d i) ≤ ∑ i, d i ∧
      ∑ i, d i - YeIPA.LP.norm2 d ^ 2 / (2 * (1 - YeIPA.LP.normInf d)) ≤ ∑ i, Real.log (1 + d i) := by
  have key : ∀ ν x : ℝ, 0 ≤ ν → ν < 1 → |x| ≤ ν →
      x - x ^ 2 / (2 * (1 - ν)) ≤ Real.log (1 + x) := by
    intro ν x hν0 hν1 hx
    have h1ν : 0 < 1 - ν := by linarith
    set φ : ℝ → ℝ := fun y => Real.log (1 + y) - y + y ^ 2 / (2 * (1 - ν)) with hφ
    have hd : ∀ y : ℝ, -1 < y →
        HasDerivAt φ (y * (y + ν) / ((1 - ν) * (1 + y))) y := by
      intro y hy
      have hy1 : 1 + y ≠ 0 := by linarith
      have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 y := (hasDerivAt_id y).const_add 1
      have h2 := h1.log hy1
      have h3 : HasDerivAt (fun y : ℝ => y ^ 2 / (2 * (1 - ν))) (2 * y / (2 * (1 - ν))) y := by
        have := ((hasDerivAt_id y).pow 2).div_const (2 * (1 - ν))
        simpa using this
      have h4 := (h2.sub (hasDerivAt_id y)).add h3
      refine h4.congr_deriv ?_
      field_simp
      ring
    have hcont : ∀ D : Set ℝ, (∀ y ∈ D, -1 < y) → ContinuousOn φ D := by
      intro D hD y hy
      exact (hd y (hD y hy)).continuousAt.continuousWithinAt
    have hφ0 : φ 0 = 0 := by simp [hφ]
    have hnn : 0 ≤ φ x := by
      rcases le_or_gt 0 x with hx0 | hx0
      · have hxν : x ≤ ν := (le_abs_self x).trans hx
        have hmono : MonotoneOn φ (Set.Icc 0 ν) := by
          apply monotoneOn_of_deriv_nonneg (convex_Icc 0 ν)
          · exact hcont _ (fun y hy => by linarith [hy.1])
          · intro y hy
            rw [interior_Icc] at hy
            exact (hd y (by linarith [hy.1])).differentiableAt.differentiableWithinAt
          · intro y hy
            rw [interior_Icc] at hy
            rw [(hd y (by linarith [hy.1])).deriv]
            have hy0 : 0 < y := hy.1
            have : 0 < 1 + y := by linarith [hy.1]
            positivity
        have := hmono ⟨le_refl 0, hν0⟩ ⟨hx0, hxν⟩ hx0
        linarith
      · have hxν : -ν ≤ x := by linarith [neg_abs_le x]
        have hanti : AntitoneOn φ (Set.Icc (-ν) 0) := by
          apply antitoneOn_of_deriv_nonpos (convex_Icc (-ν) 0)
          · exact hcont _ (fun y hy => by linarith [hy.1])
          · intro y hy
            rw [interior_Icc] at hy
            exact (hd y (by linarith [hy.1])).differentiableAt.differentiableWithinAt
          · intro y hy
            rw [interior_Icc] at hy
            rw [(hd y (by linarith [hy.1])).deriv]
            have h1 : 0 < 1 + y := by linarith [hy.1]
            have h2 : 0 ≤ y + ν := by linarith [hy.1]
            have h3 : y < 0 := hy.2
            apply div_nonpos_of_nonpos_of_nonneg
            · nlinarith
            · positivity
        have := hanti ⟨hxν, hx0.le⟩ ⟨by linarith, le_refl 0⟩ hx0.le
        linarith
    simp only [hφ] at hnn
    linarith
  have hbd : ∀ i, |d i| ≤ YeIPA.LP.normInf d := fun i =>
    le_ciSup (f := fun j => |d j|) (Set.finite_range _).bddAbove i
  have hpos : ∀ i, 0 < 1 + d i := by
    intro i
    have := hbd i
    have := neg_abs_le (d i)
    linarith
  constructor
  · apply Finset.sum_le_sum
    intro i _
    have := Real.log_le_sub_one_of_pos (hpos i)
    linarith
  · rcases isEmpty_or_nonempty (Fin n) with hn | hn
    · have h1 := sub_pos.mpr hd
      simp
      positivity
    · have hν0 : 0 ≤ YeIPA.LP.normInf d := by
        obtain ⟨i⟩ := hn
        exact (abs_nonneg _).trans (hbd i)
      have h2 : YeIPA.LP.norm2 d ^ 2 = ∑ i, d i ^ 2 := by
        unfold YeIPA.LP.norm2
        exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      rw [h2]
      have : ∑ i, d i - (∑ i, d i ^ 2) / (2 * (1 - YeIPA.LP.normInf d))
          = ∑ i, (d i - d i ^ 2 / (2 * (1 - YeIPA.LP.normInf d))) := by
        rw [Finset.sum_sub_distrib, Finset.sum_div]
      rw [this]
      apply Finset.sum_le_sum
      intro i _
      exact key _ _ hν0 hd (hbd i)
