-- Prove2me | solution 1 for ThreeSum.Parameters.switchThreshold_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:44.010509+00:00
-- url     : https://prove2.me/submissions/a5a15dc7-febf-4601-a3c9-716084cbfc78

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
theorem _root_.solution {a : ℝ} (ha : a ∈ Icc (0 : ℝ) terminalFraction) :
    switchThreshold a ≤ 941 / 350 := by
  have hden : 0 < 1 - a := by dsimp [terminalFraction] at ha; linarith [ha.2]
  rw [switchThreshold, div_le_iff₀ hden]
  dsimp [boxSaving, bandShift, terminalFraction] at *
  linarith [ha.2]
end ThreeSum.Parameters
