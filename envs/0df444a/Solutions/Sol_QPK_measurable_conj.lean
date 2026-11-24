-- Prove2me | solution 1 for QPK.measurable_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:18:55.140372+00:00
-- url     : https://prove2.me/submissions/9ed39d8b-e745-42b3-a9f1-9b82c3f29852

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarMeasureUniqueness
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_ConjugationInvariantMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Topology
open scoped ENNReal
open QPK
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace QPK
theorem _root_.solution (h : G) : Measurable (fun x : G => h * x * h⁻¹) := ((continuous_const.mul continuous_id).mul continuous_const).measurable
end QPK
