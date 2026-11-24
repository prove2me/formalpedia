-- Prove2me | solution 1 for QPK.conj_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:17:28.629624+00:00
-- url     : https://prove2.me/submissions/0beac7ca-fe47-4122-9364-fffed1a25734

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
theorem _root_.solution (g h : G) :
    (fun x : G => g * x * g⁻¹) ∘ (fun x : G => h * x * h⁻¹) = fun x => (g * h) * x * (g * h)⁻¹ := by
  funext x
  simp only [Function.comp_apply, mul_inv_rev]
  group
end QPK
