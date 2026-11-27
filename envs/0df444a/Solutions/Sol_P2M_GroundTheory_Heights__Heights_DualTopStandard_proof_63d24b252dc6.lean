-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualTopStandard_proof_63d24b252dc6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:55:41.598712+00:00
-- url     : https://prove2.me/submissions/8168bff9-8c0b-4b9d-ad8e-e833534bfee4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ScaledExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualStdBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassLinesProj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualTopStandard

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
open ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights
namespace DualTopStandard
theorem _root_.solution (hBC : DualStdBaseChange.Statement) (hGL : GrassLinesProj.Statement) :
    DualTopStandard.Statement := by
  intro K _ _ i T _ _ b hb II hi hII
  rw [hBC K i T b hb II hi hII]
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel, hGL m II hII]
end DualTopStandard
end GroundTheory.Heights₂.Heights
