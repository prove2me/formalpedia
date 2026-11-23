-- Prove2me | solution 1 for PI.QuotMeasUniqW.indicator_preimage_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:20.689038+00:00
-- url     : https://prove2.me/submissions/0e70fdf1-3455-4448-bbf5-dc2061504d4a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QmuWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QLiftIsMulLeftInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Pointwise
open scoped ENNReal
open PI PI.QuotMeasUniqW
namespace PI.QuotMeasUniqW
theorem _root_.solution {α β : Type*} (f : α → β) (s : Set β) (x : α) :
    (f ⁻¹' s).indicator (1 : α → ℝ≥0∞) x = s.indicator 1 (f x) := by
  by_cases h : f x ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show x ∈ f ⁻¹' s from h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show x ∉ f ⁻¹' s from h)]
end PI.QuotMeasUniqW
