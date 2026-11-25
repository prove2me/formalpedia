-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutRealSyzygy_flagIntegral_zero_e83a39c3e0c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:59:42.068441+00:00
-- url     : https://prove2.me/submissions/87b57b79-9ca5-4af7-9a4e-93e0cb392f80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutRealSyzygy

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace RestCutRealSyzygy
theorem _root_.solution (f N : ℕ) : RestTerms.flagIntegral f N 0 = 0 := by
  simp [RestTerms.flagIntegral]
end RestCutRealSyzygy
end GroundTheory.Heights₂.Heights
