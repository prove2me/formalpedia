-- Prove2me | solution 1 for PI.WeilQuotMeas.UnitaryGroupMassFormula.measurable_mul_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:30.751847+00:00
-- url     : https://prove2.me/submissions/d0b56948-c128-4d6a-a648-e5b128403245

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeilQuotMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_StepBruhat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_LintegralMulAvgComm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
open scoped ENNReal Pointwise
open PI PI.WeilQuotMeas PI.WeilQuotMeas.UnitaryGroupMassFormula
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
namespace PI.WeilQuotMeas.UnitaryGroupMassFormula
theorem _root_.solution : Measurable (fun p : G × H => p.1 * (p.2 : G)) := measurable_fst.mul (measurable_subtype_coe.comp measurable_snd)
end PI.WeilQuotMeas.UnitaryGroupMassFormula
