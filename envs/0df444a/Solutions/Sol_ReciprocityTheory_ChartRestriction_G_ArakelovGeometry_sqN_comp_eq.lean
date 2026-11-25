-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.sqN_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:53:13.412828+00:00
-- url     : https://prove2.me/submissions/e4b92032-a55a-4ca4-a634-0161596aae4d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} {m : ConeMetric ℂ (Ix κ)}
    (hFS : IsPullFS x e m) {z : Ix κ → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) :
    sqN (z ∘ e) = m.ρ z ^ 2 := by
  rw [hFS z hz, Real.sq_sqrt (Finset.sum_nonneg fun k _ => by positivity)]
  rfl
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
