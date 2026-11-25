-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_convex_logCover_7e1cb67a0f5e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:49:51.739379+00:00
-- url     : https://prove2.me/submissions/5cc8297d-c1c8-4dd1-96f1-5a5e9e84ec2f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {n a : ℕ} (h : a ≤ n) : Convex ℝ (logCover h) := by
  intro x hx y hy s t hs ht hst
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · have := convex_Iio (0 : ℝ) (hx.1 i) (hy.1 i) hs ht hst
    simpa using this
  · have := convex_ball (0 : ℂ) 1 (mem_ball_zero_iff.2 (hx.2 k hk))
      (mem_ball_zero_iff.2 (hy.2 k hk)) hs ht hst
    simpa using this
end GroundTheory.Heights₂.Heights.Regular
