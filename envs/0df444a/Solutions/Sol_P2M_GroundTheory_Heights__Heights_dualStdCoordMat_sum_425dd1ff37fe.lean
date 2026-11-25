-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_dualStdCoordMat_sum_425dd1ff37fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:30:35.867276+00:00
-- url     : https://prove2.me/submissions/467996b8-8e2a-4be3-afbc-209d786c856f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualStdBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_SingleMemDualLatticeStandard

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField Matrix
noncomputable section
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]
omit [DecidableEq T]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (j : Fin i) :
    ∑ t, dualStdCoordMat b () j t • (b t : Fin i → K) = Pi.single j 1 := by
  have h := congrArg (fun v : dualLattice (HermLattice.standard K i) => (v : Fin i → K))
    (b.sum_repr ⟨Pi.single j 1, single_mem_dualLattice_standard K j⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  exact h
end GroundTheory.Heights₂.Heights
