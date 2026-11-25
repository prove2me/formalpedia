-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardModelDualRank_w_ne_zero_51eba0bb76b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:19:13.537983+00:00
-- url     : https://prove2.me/submissions/32f2671b-d168-4e68-8aef-4e89cd594409

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardModelDualRank
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_S_ne_zero_fc2208a23e8b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_T_ne_zero_f2d1927e4435
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_coord_ne_zero_8ba8fb65c857

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
variable [NumberField K]
variable {T : Type}
namespace GroundTheory.Heights₂.Heights.StandardModelDualRank
theorem _root_.solution (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (t : T) : w b t ≠ 0 :=
  mul_ne_zero (mul_ne_zero (coord_ne_zero b t) S_ne_zero) T_ne_zero
end GroundTheory.Heights₂.Heights.StandardModelDualRank
