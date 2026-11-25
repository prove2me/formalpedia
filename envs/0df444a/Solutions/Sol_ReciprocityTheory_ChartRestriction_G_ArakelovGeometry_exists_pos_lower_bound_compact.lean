-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_pos_lower_bound_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:50:55.605803+00:00
-- url     : https://prove2.me/submissions/b16e8a01-c8f1-48fc-a87a-749388c08cd5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsBoundIteratedFDerivCompact
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionBasisLocalUniformBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory
open scoped ContDiff
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {E : Type*} [TopologicalSpace E] {K : Set E} (hK : IsCompact K)
    {ν : E → ℝ} (hc : ContinuousOn ν K) (hpos : ∀ y ∈ K, 0 < ν y) :
    ∃ νmin : ℝ, 0 < νmin ∧ ∀ y ∈ K, νmin ≤ ν y := by
  rcases K.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn h hc
    exact ⟨ν y, hpos y hy, fun z hz => hmin hz⟩
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
