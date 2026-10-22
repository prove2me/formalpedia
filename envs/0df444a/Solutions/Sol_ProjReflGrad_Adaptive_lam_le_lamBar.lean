-- Prove2me | solution 1 for ProjReflGrad.Adaptive.lam_le_lamBar
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:06:05.457185+00:00
-- url     : https://prove2.me/submissions/c892f35e-4286-4ae6-961a-f011f94cedad

import Mathlib
import Definitions.Def_ProjReflGrad_Adaptive_Setting

set_option autoImplicit false

open ProjReflGrad.Adaptive

lemma pra_stepCap_pos {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (F : H → H)
    (α lamBar : ℝ) (hα : 0 < α) (hbar : 0 < lamBar) (yp y : H) (taup lamp tau : ℝ)
    (htaup : 0 ≤ taup) (htau : 0 < tau) (hlamp : 0 < lamp) :
    0 < stepCap F α lamBar yp taup lamp y tau := by
  have h2 : 0 < (1 + taup) / tau * lamp := by positivity
  unfold stepCap
  split_ifs with hF
  · exact lt_min h2 hbar
  · refine lt_min ?_ (lt_min h2 hbar)
    have hpos : 0 < ‖F y - F yp‖ := norm_pos_iff.2 (sub_ne_zero.2 hF)
    have hyy : y ≠ yp := fun h => hF (by rw [h])
    have hpos2 : 0 < ‖y - yp‖ := norm_pos_iff.2 (sub_ne_zero.2 hyy)
    positivity

lemma pra_stepCap_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (F : H → H)
    (α lamBar : ℝ) (yp y : H) (taup lamp tau : ℝ) :
    stepCap F α lamBar yp taup lamp y tau ≤ lamBar := by
  unfold stepCap
  split_ifs with hF
  · exact min_le_right _ _
  · exact le_trans (min_le_right _ _) (min_le_right _ _)

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C) (F : H → H) (L : ℝ)
    (hL : 0 < L) (hC3 : ProjReflGrad.Weak.IsLipschitzMap F L)
    (α lamInit lamBar : ℝ) (hα0 : 0 < α) (hα1 : α < Real.sqrt 2 - 1) (hlamInit : 0 < lamInit)
    (hlamBar : 0 < lamBar) (x y : ℕ → H) (lam tau : ℕ → ℝ)
    (hrun : IsAdaptiveRun C F α lamInit lamBar x y lam tau) :
    ∀ n, 0 < lam n ∧ lam n ≤ lamBar ∧ 0 < tau n ∧ tau n ≤ 1 := by
  obtain ⟨hx0, hy0, hl0, ht0, hx1, hstep⟩ := hrun
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, by rw [ht0]; exact one_pos, by rw [ht0]⟩
    · rw [hl0]; unfold initStep
      split_ifs with hF
      · exact hlamBar
      · refine lt_min ?_ hlamBar
        have hpos : 0 < ‖F (x 0) - F (y 0)‖ := norm_pos_iff.2 (sub_ne_zero.2 hF)
        have hyy : x 0 ≠ y 0 := fun h => hF (by rw [h])
        have hpos2 : 0 < ‖x 0 - y 0‖ := norm_pos_iff.2 (sub_ne_zero.2 hyy)
        positivity
    · rw [hl0]; unfold initStep
      split_ifs with hF
      · exact le_refl _
      · exact min_le_right _ _
  | succ n ih =>
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    have hs := hstep (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hs
    have hcp := pra_stepCap_pos F α lamBar hα0 hlamBar (y n) ((2 : ℝ) • x (n + 1) - x n) (tau n) (lam n) 1
      ih3.le one_pos ih1
    have hcl := pra_stepCap_le F α lamBar (y n) ((2 : ℝ) • x (n + 1) - x n) (tau n) (lam n) 1
    rcases hs with ⟨-, -, hl, ht, -⟩ | ⟨-, hle, -, ht, hlam, -⟩ | ⟨-, -, htau, -, -, hlam, -⟩
    · exact ⟨by rw [hl]; exact hcp, by rw [hl]; exact hcl, by rw [ht]; exact one_pos, by rw [ht]⟩
    · exact ⟨lt_of_lt_of_le ih1 hlam.1, le_trans hlam.2 hcl, by rw [ht]; exact one_pos, by rw [ht]⟩
    · have hp2 := pra_stepCap_pos F α lamBar hα0 hlamBar (y n) (y (n + 1)) (tau n) (lam n) (tau (n + 1))
        ih3.le htau.1 ih1
      have hc2 := pra_stepCap_le F α lamBar (y n) (y (n + 1)) (tau n) (lam n) (tau (n + 1))
      exact ⟨lt_of_lt_of_le (mul_pos htau.1 ih1) hlam.1, le_trans hlam.2 hc2, htau.1, htau.2⟩
