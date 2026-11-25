-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardModelDualRank_w_eq_4239f43f32aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:19:10.626898+00:00
-- url     : https://prove2.me/submissions/81b9393a-c263-4565-963c-c2e826765bd0

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
variable [NumberField K]
variable {T : Type}
namespace GroundTheory.Heights₂.Heights.StandardModelDualRank
theorem _root_.solution (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (t : T) :
    w b t = ∑ j, embK K i ((b t : Fin i → K) j) * u K i j := by
  simp only [w, u, dualLatticeCoord, map_sum, map_mul, Finset.sum_mul, embK, RingHom.comp_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, mul_assoc, mul_assoc, mul_assoc]
end GroundTheory.Heights₂.Heights.StandardModelDualRank
