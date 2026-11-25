-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardModelDualRank_psi_X_d961fe179bbd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:19:08.513979+00:00
-- url     : https://prove2.me/submissions/f2dffed2-02bf-4627-8aaf-a4baff8e6071

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardModelDualRank

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField DualArithmeticVariety
noncomputable section
open GroundTheory.Heights₂.Heights.StandardModelDualRank
variable {K : Type} [Field K] {i : ℕ}
namespace GroundTheory.Heights₂.Heights.StandardModelDualRank
theorem _root_.solution (j : Fin i) : psi K i (X j) = u K i j := by
  simp [psi, psiA, u, dualStdModelEmb, dualStdModelS, dualStdModelT]
end GroundTheory.Heights₂.Heights.StandardModelDualRank
