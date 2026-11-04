-- Prove2me | solution 1 for ThreeSum.Parameters.phi_increment_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:11:46.116205+00:00
-- url     : https://prove2.me/submissions/33493a81-c4ee-407e-8802-d16c34671473

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
import Theorems.Thm_ThreeSum_Parameters_phi_derivative_lt_nine
import Theorems.Thm_ThreeSum_Parameters_hasDerivAt_phi

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (1 / 2)) (hv : v ∈ Icc (0 : ℝ) (1 / 2)) (huv : u < v) :
    phi v - phi u < 9 * (v - u) := by
  apply (convex_Icc (0 : ℝ) (1 / 2)).image_sub_lt_mul_sub_of_deriv_lt
    (fun y _ => (hasDerivAt_phi y).continuousAt.continuousWithinAt)
    (fun y _ => (hasDerivAt_phi y).differentiableAt.differentiableWithinAt)
    (fun y hy => ?_) u hu v hv huv
  rw [(hasDerivAt_phi y).deriv]
  exact phi_derivative_lt_nine (interior_subset hy)
end ThreeSum.Parameters
