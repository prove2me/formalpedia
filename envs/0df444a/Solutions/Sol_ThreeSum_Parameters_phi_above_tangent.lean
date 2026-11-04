-- Prove2me | solution 1 for ThreeSum.Parameters.phi_above_tangent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:40.447421+00:00
-- url     : https://prove2.me/submissions/76848e6b-2d3b-40d7-89d1-698c57372ddf

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
theorem _root_.solution {t : ℝ} (ht : 0 ≤ t) :
    phi tangentPoint + (t - tangentPoint) * phiDeriv tangentPoint ≤ phi t := by
  have hfact : phi t - (phi tangentPoint + (t - tangentPoint) * phiDeriv tangentPoint) =
      (t - tangentPoint) ^ 2 * (18 / 25 + (6 / 25) * (t + 2 * tangentPoint)) := by
    unfold phi phiDeriv
    ring
  have hnonneg : 0 ≤ (t - tangentPoint) ^ 2 *
      (18 / 25 + (6 / 25) * (t + 2 * tangentPoint)) := by
    apply mul_nonneg (sq_nonneg _)
    dsimp [tangentPoint]
    linarith
  linarith
end ThreeSum.Parameters
