-- Prove2me | solution 1 for P2M_CompanionTheory_WaveGrid_lam__anti_6a5a945442e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:08:51.820277+00:00
-- url     : https://prove2.me/submissions/b990671e-6dfa-49e0-b7ed-1c5062008124

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_PStarTie

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
theorem _root_.solution : StrictAnti lam₂ := by
  intro s t hst
  have : ((s : ℕ) : ℝ) < ((t : ℕ) : ℝ) := by exact_mod_cast hst
  simp only [lam₂]
  linarith
end CompanionTheory.WaveGrid
