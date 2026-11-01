-- Prove2me | solution 1 for ProxBundle.GPB.lemma_4_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T03:57:15.303618+00:00
-- url     : https://prove2.me/submissions/306e3a07-e6df-4fd5-825d-835c21f48283

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model
import Theorems.Thm_ProxBundle_GPB_eq_7
import Theorems.Thm_ProxBundle_GPB_lemma_A_3

open ProxBundle.GPB
open scoped InnerProductSpace RealInnerProductSpace

theorem solution {n : ℕ} (P : Instance n) (μ Mbar Lbar lam ε τ : ℝ)
    (x0 x0s : E n) (R : Run n)
    (hμ : 0 ≤ μ) (hM : 0 ≤ Mbar) (hL : 0 ≤ Lbar)
    (hA1 : P.A1 μ) (hA3 : P.A3 Mbar Lbar)
    (hlam : 0 < lam) (hε : 0 < ε)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (h29 : Cond29 μ lam ε τ Mbar Lbar)
    (hx0 : x0 ∈ P.D) (hopt : P.IsNearestOpt x0 x0s)
    (hrun : IsRun P μ lam ε τ x0 R)
    (j : ℕ) (hserious : R.t P lam j ≤ ε / 2)
    (hbefore : j = 0 ∨ ε < P.φ (R.y j) - P.φ x0s) :
    R.t P lam (j + 1) ≤ tbar Mbar Lbar lam ‖x0 - x0s‖ := by
  have hA3' := ProxBundle.GPB.lemma_A_3 P μ Mbar Lbar lam ε τ x0 x0s R hμ hM hL hA1 hA3
    hlam hε hτ0 hτ1 h29 hx0 hopt hrun j hserious hbefore
  have h7 := ProxBundle.GPB.eq_7 P μ Mbar Lbar hμ hM hL hA1 hA3
  obtain ⟨hserbr, -, hprox1, -, hymin1⟩ := hrun.2.2 (j + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hserbr
  obtain ⟨hxc, -, hlow⟩ := hserbr hserious
  have hxjD : R.x j ∈ P.D := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h, hrun.1]; exact hx0
    · exact (hrun.2.2 j h).2.2.1.1
  have hxj1D : R.x (j + 1) ∈ P.D := hprox1.1
  have hy : P.φ (R.y (j + 1)) ≤ P.φ (R.x (j + 1)) := hymin1 (j + 1) le_rfl
  have ht : R.t P lam (j + 1) = P.φ (R.y (j + 1)) -
      (R.Γ (j + 1) (R.x (j + 1)) + ‖R.x (j + 1) - R.xc (j + 1)‖ ^ 2 / (2 * lam)) := by
    unfold Run.t Run.m; rw [if_neg (by omega)]
  have hlo := (hlow (R.x (j + 1)) hxj1D).1
  have he7 := h7 (R.x (j + 1)) hxj1D (R.x j) hxjD
  set a := ‖R.x (j + 1) - R.x j‖ with ha
  set B := max 1 (2 * lam * Lbar) * ‖x0 - x0s‖ + lam * Mbar with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ max 1 (2 * lam * Lbar) := le_trans zero_le_one (le_max_left _ _)
    positivity
  have haB : a ≤ 2 * Real.sqrt 2 * B := by
    rw [ha, norm_sub_rev]; exact hA3'
  have ha2 : a ^ 2 ≤ 8 * B ^ 2 := by
    have h0 : 0 ≤ a := norm_nonneg _
    have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have := pow_le_pow_left₀ h0 haB 2
    nlinarith
  have hq : 0 ≤ ‖R.x (j + 1) - R.xc (j + 1)‖ ^ 2 / (2 * lam) := by positivity
  unfold Instance.φ at hy
  unfold Instance.ellf at hlo he7
  have hamg : 2 * Mbar * a ≤ Mbar ^ 2 + a ^ 2 := by nlinarith [sq_nonneg (Mbar - a)]
  have hfin : Mbar ^ 2 + (Lbar / 2 + 1) * a ^ 2 ≤ tbar Mbar Lbar lam ‖x0 - x0s‖ := by
    unfold tbar
    rw [← hB]
    have := mul_le_mul_of_nonneg_left ha2 (by positivity : (0:ℝ) ≤ Lbar / 2 + 1)
    nlinarith
  rw [ht]
  unfold Instance.φ
  linarith
