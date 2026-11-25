-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.volume_axes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:16:23.085777+00:00
-- url     : https://prove2.me/submissions/c6e8a2e2-44a9-45cf-8ca0-211b45406e07

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IntegrableUnitIndicator

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
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution : volume {z : ℂ | z.im = 0 ∨ z.re = 0} = 0 := by
  have e := Complex.volume_preserving_equiv_real_prod
  have h1 : volume {z : ℂ | z.im = 0} = 0 := by
    have hs : {z : ℂ | z.im = 0} = Complex.measurableEquivRealProd ⁻¹' (Set.univ ×ˢ {0}) := by
      first
      | (ext z; exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩)
      | (ext z; simp [Complex.measurableEquivRealProd])
    rw [hs, e.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have h2 : volume {z : ℂ | z.re = 0} = 0 := by
    have hs : {z : ℂ | z.re = 0} = Complex.measurableEquivRealProd ⁻¹' ({0} ×ˢ Set.univ) := by
      first
      | (ext z; exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩)
      | (ext z; simp [Complex.measurableEquivRealProd])
    rw [hs, e.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hu : {z : ℂ | z.im = 0 ∨ z.re = 0} = {z : ℂ | z.im = 0} ∪ {z : ℂ | z.re = 0} := rfl
  rw [hu]
  exact measure_union_null h1 h2
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
