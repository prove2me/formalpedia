-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardModelDualRank_coord_ne_zero_8ba8fb65c857
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:56.524794+00:00
-- url     : https://prove2.me/submissions/a2360f46-119c-4504-a435-69061359a68c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardModelDualRank
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_dualLatticeCoord_eq_ca49334a53b1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_evalForm_ne_zero_eeeb6c3d9f4a


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
    dualStdModelEmb K i (dualLatticeCoord b ⟨(), t⟩) ≠ 0 := by
  rw [map_ne_zero_iff _ (dualStdModelEmb K i).injective, dualLatticeCoord_eq]
  exact evalForm_ne_zero fun h => b.ne_zero t ((Submodule.coe_eq_zero).mp h)
end GroundTheory.Heights₂.Heights.StandardModelDualRank
