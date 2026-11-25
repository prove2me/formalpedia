-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KCoord_finMean_sub_2af85f626cdf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:00:53.818278+00:00
-- url     : https://prove2.me/submissions/e55ac8b5-9c26-46e0-befa-376cfcee2695

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
theorem _root_.solution (f h : S → ℝ) : finMean (fun s => f s - h s) = finMean f - finMean h := by
  simp [finMean, Finset.sum_sub_distrib, sub_div]
end GroundTheory.Heights₂.Heights.KCoord
