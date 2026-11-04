-- Prove2me | solution 1 for ThreeSum.Parameters.phi_step_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:16:24.800645+00:00
-- url     : https://prove2.me/submissions/610e5780-3ea4-4a23-a7cf-a0f1e050ce6d

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
import Theorems.Thm_ThreeSum_Parameters_phi_increment_bound

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution {u v m K : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (1 / 2)) (hv : v ∈ Icc (0 : ℝ) (1 / 2))
    (hm : 0 < m) (hstep : v - u = 1 / m) (hprev : phi u < K) :
    phi v < K + 9 / m := by
  have huv : u < v := by
    have : 0 < 1 / m := by positivity
    linarith
  have h := phi_increment_bound hu hv huv
  rw [hstep] at h
  rw [show 9 / m = 9 * (1 / m) by ring]
  linarith
end ThreeSum.Parameters
