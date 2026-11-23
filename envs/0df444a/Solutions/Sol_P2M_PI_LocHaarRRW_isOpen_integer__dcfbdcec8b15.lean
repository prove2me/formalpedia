-- Prove2me | solution 1 for P2M_PI_LocHaarRRW_isOpen_integer__dcfbdcec8b15
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:26.76569+00:00
-- url     : https://prove2.me/submissions/04647e8b-6bba-40c7-8b54-9d75cd23ff1c

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
theorem _root_.solution : IsOpen (𝒪[K] : Set K) := Valuation.isOpen_integer
end PI.LocHaarRRW
