-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitA.small_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:15:41.860799+00:00
-- url     : https://prove2.me/submissions/a24b71b2-ef61-432a-8667-68cb1fbae4bb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_UnitarizeA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.UnitA
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] (μ : Measure G)
variable {μ}
variable [μ.IsMulRightInvariant] [SFinite μ]
namespace ReciprocityTheory.ChartRestriction.DS.UnitA
theorem _root_.solution {D : ℂ} {C : ℝ} (h : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖D‖ ≤ t * C) : D = 0 := by
  by_contra hD
  have hpos : 0 < ‖D‖ := norm_pos_iff.mpr hD
  have h1 := h 1 one_pos le_rfl
  have hC : 0 < C := by linarith
  have hC0 : C ≠ 0 := hC.ne'
  have ht0 : 0 < min 1 (‖D‖ / (2 * C)) := lt_min one_pos (div_pos hpos (by linarith))
  have ht1 : min 1 (‖D‖ / (2 * C)) ≤ 1 := min_le_left _ _
  have ht2 : min 1 (‖D‖ / (2 * C)) ≤ ‖D‖ / (2 * C) := min_le_right _ _
  have h2 := h _ ht0 ht1
  have h3 : min 1 (‖D‖ / (2 * C)) * C ≤ ‖D‖ / 2 := by
    calc min 1 (‖D‖ / (2 * C)) * C ≤ ‖D‖ / (2 * C) * C := mul_le_mul_of_nonneg_right ht2 hC.le
      _ = ‖D‖ / 2 := by field_simp <;> ring
  linarith
end ReciprocityTheory.ChartRestriction.DS.UnitA
