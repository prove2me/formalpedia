-- Prove2me | solution 1 for QPK.exists_pos_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:03:45.47931+00:00
-- url     : https://prove2.me/submissions/d9107e13-55b0-4e63-a317-8d5d98ff2994

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
theorem _root_.solution (μ : Measure G) [SigmaFinite μ] (h0 : μ ≠ 0) :
    ∃ A : Set G, μ A ≠ 0 ∧ μ A ≠ ⊤ := by
  by_contra hc
  push_neg at hc
  apply h0
  rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets μ]
  apply measure_iUnion_null
  intro n
  by_contra hn
  exact (measure_spanningSets_lt_top μ n).ne (hc _ hn)
end QPK
