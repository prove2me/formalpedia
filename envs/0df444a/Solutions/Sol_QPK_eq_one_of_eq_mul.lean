-- Prove2me | solution 1 for QPK.eq_one_of_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:13:43.115137+00:00
-- url     : https://prove2.me/submissions/6e263622-f661-41d5-b2ba-b7f30f4f9501

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarMeasureUniqueness
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_SiegelMeasureDefinition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology Set
open scoped ENNReal Pointwise
open QPK
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace QPK
theorem _root_.solution {c x : ℝ≥0∞} (h0 : x ≠ 0) (ht : x ≠ ⊤) (h : x = c * x) : c = 1 := by
  have h' : x * c = x * 1 := by rw [mul_one, mul_comm]; exact h.symm
  exact (ENNReal.mul_right_inj h0 ht).mp h'
end QPK
