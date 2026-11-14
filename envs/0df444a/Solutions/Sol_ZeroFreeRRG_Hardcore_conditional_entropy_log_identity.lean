-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.conditional_entropy_log_identity
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:46:41.198201+00:00
-- url     : https://prove2.me/submissions/470b9221-e439-472b-9679-40a65e77db39

import Mathlib
set_option autoImplicit false

theorem solution (S L R T : ℝ)
    (hS : S=0 → T=0) (hL : L=0 → T=0) (hR : R=0 → T=0) :
    T * Real.log (L*R/S) = T*Real.log L + T*Real.log R - T*Real.log S := by
  by_cases hT : T=0
  · simp [hT]
  · have hS' : S ≠ 0 := fun h => hT (hS h)
    have hL' : L ≠ 0 := fun h => hT (hL h)
    have hR' : R ≠ 0 := fun h => hT (hR h)
    rw [Real.log_div (mul_ne_zero hL' hR') hS', Real.log_mul hL' hR']
    ring
