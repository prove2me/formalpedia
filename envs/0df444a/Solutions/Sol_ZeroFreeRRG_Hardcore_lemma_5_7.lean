-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.lemma_5_7
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:37:43.795497+00:00
-- url     : https://prove2.me/submissions/f59b2032-d58c-4472-831d-5998844cd3c8

import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_shearer_disc
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_deterministic_zero_free
import Mathlib
open ZeroFreeRRG.Hardcore
open scoped Classical

theorem solution (d : ℕ) (hd : 3 ≤ d) :
    (∀ (V : Type) [Fintype V] (G : SimpleGraph V), (∀ v, G.degree v ≤ d) →
      ∀ lam : ℂ, ‖lam‖ < ((d : ℝ) - 1) ^ (d - 1) / (d : ℝ) ^ d → hardcoreZfug G lam ≠ 0) ∧
    (∀ q : ℕ, 2 ≤ q → ∀ (V : Type) [Fintype V] (G : SimpleGraph V), (∀ v, G.degree v ≤ d) →
      ∀ β : ℂ, ‖β - 1‖ < 0.35 / (d : ℝ) → pottsZ q G β ≠ 0) := by
  constructor
  · intro V _ G hG lam hlam
    exact hardcore_shearer_disc G d hd hG lam hlam
  · exact potts_deterministic_zero_free d hd
