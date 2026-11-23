-- Prove2me | solution 1 for PI.VolStabSW.mem_smulSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:01:09.64844+00:00
-- url     : https://prove2.me/submissions/1f88b7f4-e0d3-4469-91d4-88a29e4baf88

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_MeasureEqOfCos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_EventuallySmulSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Topology Filter Set
variable {K V X : Type} [Field K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]
  [AddCommGroup X] [Module K X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul K X]
omit [TopologicalSpace K]
namespace PI.VolStabSW
theorem _root_.solution {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) (z : W) :
    z ∈ smulSub t P ↔ ∃ p ∈ P, t • p = z := by
  simp only [smulSub, AddSubgroup.mem_map, DistribMulAction.toAddMonoidHom_apply]
end PI.VolStabSW
