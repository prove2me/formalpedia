-- Prove2me | solution 1 for PI.LocHaarRRW.isCompact_integer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:33.952198+00:00
-- url     : https://prove2.me/submissions/a8ebd96d-325d-4efe-8622-7cb29a63673c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_ExistsHaarOfSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel MeasureTheory Topology Polynomial
open PI PI.LocHaarRRW
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace PI.LocHaarRRW
theorem _root_.solution : IsCompact (𝒪[K] : Set K) :=
  isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace 𝒪[K])
end PI.LocHaarRRW
