-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardModelDualRank_psi_injective_f732774ce2a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:14:16.549951+00:00
-- url     : https://prove2.me/submissions/ef8e34a1-e0bb-4f92-8635-428670c824cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardModelDualRank
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_psiA_injective_d94cf10a548d

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
theorem _root_.solution : Function.Injective (psi K i) := by
  rw [psi, RingHom.coe_comp]
  exact (IsFractionRing.injective (MvPolynomial Unit (MvPolynomial Unit (ProjField K i)))
    (dualStdModelField K i)).comp psiA_injective
end GroundTheory.Heights₂.Heights.StandardModelDualRank
