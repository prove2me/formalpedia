-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_ballSet_subset_closedBall_a60a8a60db99
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:18:47.867344+00:00
-- url     : https://prove2.me/submissions/b4a377c5-c904-4098-8bfa-5a8a1015e10c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Measure Set
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean
namespace GroundTheory.Heights₂.Heights.SphereMean
theorem _root_.solution (n : ℕ) : ballSet n 1 ⊆ Metric.closedBall 0 1 := by
  intro x hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  have h1 : ‖x j‖ ^ 2 ≤ sqNorm x :=
    Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ‖x j‖ ^ 2 < 1 := lt_of_le_of_lt h1 hx
  nlinarith [norm_nonneg (x j)]
end GroundTheory.Heights₂.Heights.SphereMean
