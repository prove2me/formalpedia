-- Prove2me | solution 1 for OpaqueQueue.Equilibrium.phi_strictAnti
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:57:17.384113+00:00
-- url     : https://prove2.me/submissions/a1b30f0a-aca7-45e9-87ef-80c86e295ed2

import Mathlib
import Definitions.Def_OpaqueQueue_Equilibrium_Model
open OpaqueQueue.Equilibrium

theorem solution(P : Params) (hS : P.Standing) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : StrictAnti (phi P x) := by
  obtain ⟨hl, hm, hC, hpR, hθ⟩ := hS
  obtain ⟨hx0, hx1⟩ := hx
  intro n m hnm
  unfold phi
  have hv : v P m / P.θ < v P n / P.θ := by
    apply (div_lt_div_iff_of_pos_right hθ).2
    unfold v
    have h1 : (n:ℝ) < m := by exact_mod_cast hnm
    have hc : 0 < P.C / P.mu := div_pos hC hm
    nlinarith
  have hE := Real.exp_lt_exp.2 hv
  have ha : 0 < Real.exp (v P m / P.θ) := Real.exp_pos _
  set a := Real.exp (v P m / P.θ)
  set b := Real.exp (v P n / P.θ)
  have pos : ∀ c : ℝ, 0 < c → 0 < x * c + 1 - x := by
    intro c hc
    rcases eq_or_lt_of_le hx1 with h | h
    · subst h; linarith
    · nlinarith [mul_nonneg hx0 hc.le]
  have hda : 0 < x * a + 1 - x := pos a ha
  have hb : 0 < b := lt_trans ha hE
  have hdb : 0 < x * b + 1 - x := pos b hb
  rw [div_lt_div_iff₀ hda hdb]
  nlinarith
