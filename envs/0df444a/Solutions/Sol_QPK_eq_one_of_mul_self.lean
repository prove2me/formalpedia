-- Prove2me | solution 1 for QPK.eq_one_of_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:03:43.762157+00:00
-- url     : https://prove2.me/submissions/3d76f80c-a720-4af7-ac30-90f101fb4f3a

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
theorem _root_.solution {c : ℝ≥0∞} (h : c * c = 1) : c = 1 := by
  rcases lt_trichotomy c 1 with hlt | heq | hgt
  · have h1 : c * c ≤ c * 1 := by gcongr
    rw [mul_one] at h1
    exact absurd h (ne_of_lt (lt_of_le_of_lt h1 hlt))
  · exact heq
  · have h1 : c * 1 ≤ c * c := by gcongr
    rw [mul_one] at h1
    exact absurd h (ne_of_gt (lt_of_lt_of_le hgt h1))
end QPK
