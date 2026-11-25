-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesIdealStdIndex_proof_6b977d9b42dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:36:47.89198+00:00
-- url     : https://prove2.me/submissions/e14cecbd-41e7-4387-bfc7-a288999f9607

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesIdealStdIndex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesIdealStdIndex_idealLattice_toAddSubgroup_d2db4e91f501

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
open NumberField
open scoped nonZeroDivisors
open KLinesIdealStdIndex
namespace GroundTheory.Heights₂.Heights
namespace LinesIdealStdIndex
theorem _root_.solution (h1 : LinesGenIndexPi.Statement) (h2 : LinesStdPi.Statement) :
    LinesIdealStdIndex.Statement := by
  intro K _ _ k a
  rw [idealLattice_toAddSubgroup, h2 K k, h1 (Fin k) K]
  rfl
end LinesIdealStdIndex
end GroundTheory.Heights₂.Heights
