-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplFirstRow_intVec_ne_zero_77209a029981
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:45:59.61015+00:00
-- url     : https://prove2.me/submissions/6dd29647-9408-4304-9ae4-a9add412f859

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplFirstRow

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
open GroundTheory.Heights₂.Heights.PSymplFirstRow
namespace GroundTheory.Heights₂.Heights.PSymplFirstRow
theorem _root_.solution {ι : Type*} {v : ι → ℤ} (hv : v ≠ 0) : intVec v ≠ 0 := by
  intro h
  apply hv
  funext i
  have := congrFun h i
  simpa [intVec] using this
end GroundTheory.Heights₂.Heights.PSymplFirstRow
