-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PGaussPacking_pairwiseDisjoint_balls_5423df6c962a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:45:51.85919+00:00
-- url     : https://prove2.me/submissions/8c1854c0-13d0-4450-b244-e1421a25e46f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussPacking

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
open MeasureTheory Metric
open GroundTheory.Heights₂.Heights.PGaussPacking
namespace GroundTheory.Heights₂.Heights.PGaussPacking
theorem _root_.solution {n : ℕ} (s : Finset (EuclideanSpace ℝ (Fin n))) {δ : ℝ}
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ ‖x - y‖) :
    (s : Set (EuclideanSpace ℝ (Fin n))).PairwiseDisjoint (fun x => ball x (δ / 2)) := by
  intro x hx y hy hxy
  apply ball_disjoint_ball
  rw [dist_eq_norm]
  linarith [hsep x hx y hy hxy]
end GroundTheory.Heights₂.Heights.PGaussPacking
