-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KAlt_frobDim_eq_c066fd4b76d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:00:18.430967+00:00
-- url     : https://prove2.me/submissions/8c2a94a4-9630-416a-b000-b4d3f20718af

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltFrob

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
open Finset
open GroundTheory.Heights₂.Heights.KAlt
namespace GroundTheory.Heights₂.Heights.KAlt
theorem _root_.solution {r : ℕ} (la : Fin r → ℕ) :
    frobDim la = ((∑ a, la a).factorial : ℚ) * frobDelta la /
      ∏ a : Fin r, ((la a + (r - 1 - a)).factorial : ℚ) := rfl
end GroundTheory.Heights₂.Heights.KAlt
