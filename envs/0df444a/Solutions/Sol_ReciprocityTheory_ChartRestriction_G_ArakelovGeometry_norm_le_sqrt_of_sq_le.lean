-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.norm_le_sqrt_of_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:09:38.507198+00:00
-- url     : https://prove2.me/submissions/e1859a63-9297-48d5-9757-77da8f0b47bf

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
theorem _root_.solution {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (h : a ^ 2 ≤ b * t ^ 2) : a ≤ Real.sqrt b * t := by
  calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ Real.sqrt (b * t ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt b * t := by rw [Real.sqrt_mul hb, Real.sqrt_sq ht]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
