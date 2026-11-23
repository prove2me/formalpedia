-- Prove2me | solution 1 for PI.VolStabS.mem_smulSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:09.026379+00:00
-- url     : https://prove2.me/submissions/476af0ba-88b4-4840-8062-e286abd455b5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_MeasureEqOfCos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_EventuallySmulSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open Topology Filter Set
variable {K V X : Type} [Field K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]
  [AddCommGroup X] [Module K X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul K X]
omit [TopologicalSpace K]
namespace PI.VolStabS
theorem _root_.solution {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) (z : W) :
    z ∈ smulSub t P ↔ ∃ p ∈ P, t • p = z := by
  simp [smulSub, AddSubgroup.mem_map]
end PI.VolStabS
