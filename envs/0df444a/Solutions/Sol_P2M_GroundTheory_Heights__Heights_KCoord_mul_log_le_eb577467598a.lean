-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KCoord_mul_log_le_eb577467598a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:00:54.801363+00:00
-- url     : https://prove2.me/submissions/6f705c1d-6d75-4c3d-b6aa-f2b8958d6f91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CoordWeak

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
open Real
open GroundTheory.Heights₂.Heights.KCoord
namespace GroundTheory.Heights₂.Heights.KCoord
theorem _root_.solution (G a : ℝ) (hG : 0 ≤ G) (ha : 0 < a) :
    G * log (1 + a) ≤ π / 192 * a ^ 2 + 48 / π * G ^ 2 := by
  have h1 : log (1 + a) ≤ a := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + a by linarith)
    linarith
  have h2 : G * log (1 + a) ≤ G * a := mul_le_mul_of_nonneg_left h1 hG
  have hpi : 0 < π := Real.pi_pos
  have h3 : π / 192 * a ^ 2 + 48 / π * G ^ 2 - G * a = (π * a - 96 * G) ^ 2 / (192 * π) := by
    field_simp
    ring
  have h4 : 0 ≤ (π * a - 96 * G) ^ 2 / (192 * π) := by positivity
  linarith
end GroundTheory.Heights₂.Heights.KCoord
