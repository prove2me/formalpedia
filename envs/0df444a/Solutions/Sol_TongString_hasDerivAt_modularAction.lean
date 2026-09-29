-- Prove2me | solution 1 for TongString.hasDerivAt_modularAction
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T14:58:46.893765+00:00
-- url     : https://prove2.me/submissions/9d52969e-2b9d-4e81-951e-798114a69c09

import Mathlib
import Definitions.Def_TongString_modular_action

open TongString in
theorem solution (a b c d : ℤ) (h : a * d - b * c = 1) (τ : ℂ) (hτ : 0 < τ.im) :
    HasDerivAt (modularAction a b c d) (1 / (c * τ + d) ^ 2) τ := by
  have hne : (c : ℂ) * τ + d ≠ 0 := by
    intro h0
    by_cases hc : c = 0
    · subst hc
      simp at h0
      subst h0
      simp at h
    · have him := congrArg Complex.im h0
      simp at him
      rcases him with h1 | h1
      · exact hc h1
      · linarith
  have hN : HasDerivAt (fun z : ℂ => (a : ℂ) * z + b) (a : ℂ) τ := by
    simpa using ((hasDerivAt_id τ).const_mul (a : ℂ)).add_const (b : ℂ)
  have hD : HasDerivAt (fun z : ℂ => (c : ℂ) * z + d) (c : ℂ) τ := by
    simpa using ((hasDerivAt_id τ).const_mul (c : ℂ)).add_const (d : ℂ)
  have hQ := hN.div hD hne
  have hC : ((a : ℂ) * d - b * c) = 1 := by exact_mod_cast h
  have heq : ((a : ℂ) * ((c : ℂ) * τ + d) - ((a : ℂ) * τ + b) * c) / ((c : ℂ) * τ + d) ^ 2
      = 1 / ((c : ℂ) * τ + d) ^ 2 := by
    congr 1
    linear_combination hC
  rw [heq] at hQ
  show HasDerivAt (fun z : ℂ => ((a : ℂ) * z + b) / ((c : ℂ) * z + d)) _ τ
  exact hQ
