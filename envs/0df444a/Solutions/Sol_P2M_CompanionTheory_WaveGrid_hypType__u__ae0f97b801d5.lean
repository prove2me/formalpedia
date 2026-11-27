-- Prove2me | solution 1 for P2M_CompanionTheory_WaveGrid_hypType__u__ae0f97b801d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:03:30.340057+00:00
-- url     : https://prove2.me/submissions/57a67e04-88ce-4544-8e25-59d30b68a878

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
theorem _root_.solution : HypType P₂.k P₂.r lam₂ P₂.u' 41 := by
  convert hypType₂ 40 (by norm_num) (by norm_num) using 1
  funext i
  simp only [P₂]
  split_ifs <;> norm_num
end CompanionTheory.WaveGrid
