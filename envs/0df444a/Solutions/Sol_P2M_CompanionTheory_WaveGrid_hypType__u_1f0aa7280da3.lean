-- Prove2me | solution 1 for P2M_CompanionTheory_WaveGrid_hypType__u_1f0aa7280da3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:58:18.001722+00:00
-- url     : https://prove2.me/submissions/0d3e19b6-ce13-401d-9003-f8c78af417a4

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_PStarTie
import Theorems.Thm_P2M_CompanionTheory_WaveGrid_hypType__bc1b63aaa92d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt Finset GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
namespace CompanionTheory.WaveGrid
theorem _root_.solution : HypType P₂.k P₂.r lam₂ P₂.u 41 := by
  convert hypType₂ 20 (by norm_num) (by norm_num) using 1
  funext i
  simp only [P₂]
  split_ifs <;> norm_num
end CompanionTheory.WaveGrid
