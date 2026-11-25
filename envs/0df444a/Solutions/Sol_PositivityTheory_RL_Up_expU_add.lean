-- Prove2me | solution 1 for PositivityTheory.RL.Up.expU_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:26.914232+00:00
-- url     : https://prove2.me/submissions/4e375870-0d3c-46b2-932f-6b879e464d77

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GroupGeneratedByExp
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix Filter Topology
open PositivityTheory PositivityTheory.RL PositivityTheory.RL.Up
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
namespace PositivityTheory.RL.Up
theorem _root_.solution (Z : 𝔸) (s t : ℝ) : expU ((s + t) • Z) = expU (s • Z) * expU (t • Z) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  refine Units.ext ?_
  show NormedSpace.exp _ = NormedSpace.exp _ * NormedSpace.exp _
  rw [add_smul, NormedSpace.exp_add_of_commute (((Commute.refl Z).smul_left s).smul_right t)]
end PositivityTheory.RL.Up
