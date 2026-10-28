-- Prove2me | solution 1 for TiltingFTT.Optimal.welfare_24_25
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T00:49:29.627484+00:00
-- url     : https://prove2.me/submissions/d5fdc970-98e1-4ce6-84fb-f77cd5ea6fb0

import Mathlib
import Definitions.Def_TiltingFTT_Optimal_Model

open TiltingFTT.Optimal in
theorem solution (P : Firm) (τ TL VH VL v : ℝ) :
    welfare P τ (P.δU * P.FH) (P.δU * P.FL) 1 1 P.FH P.FL = Wstar P ∧
    sepWelfare P τ 1 TL = Wstar P - (1 - P.β) * (P.δI - P.δU) * (1 - TL) * P.FL ∧
    poolWelfare P τ 1 =
      Wstar P - P.δI * (P.β * (P.FH - P.FbH) + (1 - P.β) * (P.FL - P.FbL)) ∧
    (Spec23 P VH VL v → poolWelfare P τ 1 = Wstar P - P.δI * v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [welfare, Wstar]; ring
  · simp only [sepWelfare, welfare, Wstar]; ring
  · simp only [poolWelfare, welfare, Wstar]; ring
  · rintro ⟨-, -, hH, hL, hbH, hbL, -, -⟩
    simp only [poolWelfare, welfare, Wstar, hH, hL, hbH, hbL]; ring
