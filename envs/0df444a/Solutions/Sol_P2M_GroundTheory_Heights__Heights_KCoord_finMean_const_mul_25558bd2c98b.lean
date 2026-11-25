-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KCoord_finMean_const_mul_25558bd2c98b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:00:50.234134+00:00
-- url     : https://prove2.me/submissions/6d39ebcd-c1cd-4666-8876-d13c57f1e676

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
variable {S : Type*} [Fintype S]
namespace GroundTheory.Heights₂.Heights.KCoord
theorem _root_.solution (c : ℝ) (f : S → ℝ) : finMean (fun s => c * f s) = c * finMean f := by
  simp [finMean, ← Finset.mul_sum, mul_div_assoc]
end GroundTheory.Heights₂.Heights.KCoord
