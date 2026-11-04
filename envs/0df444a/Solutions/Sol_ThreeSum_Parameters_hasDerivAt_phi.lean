-- Prove2me | solution 1 for ThreeSum.Parameters.hasDerivAt_phi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:59:42.293625+00:00
-- url     : https://prove2.me/submissions/77be171c-d4f0-45b4-9f98-8225cda4d9af

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
theorem _root_.solution (t : ℝ) : HasDerivAt phi (phiDeriv t) t := by
  have hd := (((hasDerivAt_id t).const_mul (799 / 100)).add
    (((hasDerivAt_id t).pow 2).const_mul (18 / 25))).add
      (((hasDerivAt_id t).pow 3).const_mul (6 / 25))
  change HasDerivAt phi _ t at hd
  apply hd.congr_deriv
  dsimp [phiDeriv]
  ring
end ThreeSum.Parameters
