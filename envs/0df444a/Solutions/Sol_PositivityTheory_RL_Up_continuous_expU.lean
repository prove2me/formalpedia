-- Prove2me | solution 1 for PositivityTheory.RL.Up.continuous_expU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:33:41.465263+00:00
-- url     : https://prove2.me/submissions/3dd9a77c-4476-459b-b2fb-f56f8aa3da00

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
theorem _root_.solution (Z : 𝔸) : Continuous fun t : ℝ => expU (t • Z) :=
  Units.isOpenEmbedding_val.isInducing.continuous_iff.2
    (continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const (𝕂 := ℝ) Z t).continuousAt)
end PositivityTheory.RL.Up
