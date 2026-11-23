-- Prove2me | solution 1 for PI.VolStabS.coe_smulSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:08:36.074538+00:00
-- url     : https://prove2.me/submissions/096fc9d3-20e3-4676-a392-34132c8b76bf

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
namespace PI.VolStabS
theorem _root_.solution {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) :
    (smulSub t P : Set W) = (fun p => t • p) '' (P : Set W) := by
  ext z
  simp [smulSub, AddSubgroup.coe_map]
end PI.VolStabS
