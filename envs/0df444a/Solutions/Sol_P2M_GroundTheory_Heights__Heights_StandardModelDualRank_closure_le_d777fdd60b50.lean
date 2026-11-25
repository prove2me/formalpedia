-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardModelDualRank_closure_le_d777fdd60b50
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:29.25601+00:00
-- url     : https://prove2.me/submissions/bf7482d6-4851-4d6b-bdf7-2a5affc8dbbd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardModelDualRank
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_psi_X_d961fe179bbd

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
theorem _root_.solution : Subring.closure (Set.range (u K i)) ≤ (psiZ K i).range :=
  (Subring.closure_le).mpr (by rintro _ ⟨j, rfl⟩; exact ⟨X j, by simp [psiZ, psi_X]⟩)
end GroundTheory.Heights₂.Heights.StandardModelDualRank
