-- Prove2me | solution 1 for ThreeSum.Parameters.cost_ledger_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:45.107743+00:00
-- url     : https://prove2.me/submissions/e46a863d-93ba-4a91-ad35-62c080141d7f

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution {e k h : ℝ} (he0 : 4 < e) (he1 : e < 19 / 4)
    (hk : k < kappaCap) (hh : h < 1 / 4) :
    2 * epsilon * e < 19 / 10 ∧
    1 + epsilon * (e - bandShift) < 49 / 25 ∧
    2 - epsilon * boxSaving = 9809 / 5000 ∧
    2 - epsilon * (1 / 2 + bandShift - h) < 49 / 25 ∧
    2 - epsilon * (1 / 2 - bandShift - k - entropyRatio * (1 + boxSaving - 2 * bandShift))
      < certificateExponent ∧
    2 - epsilon * (terminalFraction - 1 / 2 - bandShift - k) < 19603 / 10000 ∧
    epsilon * (8 / 5) * (e + 1 / 2) < 42 / 25 ∧
    2 + epsilon * (4 / 5 - (2 / 5) * e - 2 * bandShift) < 93 / 50 ∧
    1 + epsilon * (1 / 2 - bandShift) = 111 / 100 ∧
    2 - epsilon * (e + bandShift) < 121 / 100 ∧
    2 - 2 * epsilon * (e + bandShift) < 21 / 50 ∧
    epsilon * (e + bandShift) < 1 := by
  dsimp [epsilon, bandShift, boxSaving, entropyRatio, terminalFraction,
    certificateExponent, kappaCap] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
end ThreeSum.Parameters
