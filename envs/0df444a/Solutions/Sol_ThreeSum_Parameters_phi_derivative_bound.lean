-- Prove2me | solution 1 for ThreeSum.Parameters.phi_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:36.05402+00:00
-- url     : https://prove2.me/submissions/37ed71e2-2a85-4b5a-a403-2f51793b8280

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
theorem _root_.solution {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    phiDeriv t ≤ (889 / 100 : ℝ) := by
  dsimp [phiDeriv]
  have ht2 : t ^ 2 ≤ (1 / 4 : ℝ) := by
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  nlinarith [ht.1, ht.2]
end ThreeSum.Parameters
