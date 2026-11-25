-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.measurable_indicator_usc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:46.806075+00:00
-- url     : https://prove2.me/submissions/f76a2089-3adc-4dab-8bc4-a28feb041df5

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set Real
open scoped ContDiff
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} (hU : IsOpen U)
    (hφ : UpperSemicontinuousOn φ U) : Measurable (U.indicator φ) := by
  refine measurable_of_Iio fun a => ?_
  have hO : IsOpen {x | x ∈ U ∧ φ x < a} := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨hxU, hx⟩
    have h1 := hφ x hxU _ hx
    rw [nhdsWithin_eq_nhds.2 (hU.mem_nhds hxU)] at h1
    filter_upwards [h1, hU.mem_nhds hxU] with y hy hyU using ⟨hyU, hy⟩
  have : U.indicator φ ⁻¹' Iio a = {x | x ∈ U ∧ φ x < a} ∪ (Uᶜ ∩ {_x | (0 : ℝ) < a}) := by
    ext x
    by_cases hx : x ∈ U <;> simp [hx, Set.indicator]
  rw [this]
  exact hO.measurableSet.union (hU.measurableSet.compl.inter (MeasurableSet.const _))
end ReciprocityTheory.AnForm.A
