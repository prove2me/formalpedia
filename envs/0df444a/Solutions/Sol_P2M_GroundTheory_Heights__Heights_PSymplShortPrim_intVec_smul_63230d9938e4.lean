-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplShortPrim_intVec_smul_63230d9938e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:46:21.784902+00:00
-- url     : https://prove2.me/submissions/5ff2f015-b4ab-42d9-897b-7e3c0fd11c42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplShortPrim

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
open Matrix
open GroundTheory.Heights₂.Heights.PSymplShortPrim
namespace GroundTheory.Heights₂.Heights.PSymplShortPrim
theorem _root_.solution {ι : Type} (m : ℤ) (w : ι → ℤ) : intVec (m • w) = (m : ℝ) • intVec w := by
  funext i
  simp [intVec]
end GroundTheory.Heights₂.Heights.PSymplShortPrim
