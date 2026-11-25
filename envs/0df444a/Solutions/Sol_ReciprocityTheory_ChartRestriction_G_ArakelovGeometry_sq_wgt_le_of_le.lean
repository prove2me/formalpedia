-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.sq_wgt_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:53:17.321995+00:00
-- url     : https://prove2.me/submissions/399f403f-65e1-443c-9b5a-6e5a3eb87874

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
theorem _root_.solution {m : ConeMetric ℂ (Ix κ)} {n : ℕ} {z : Ix κ → ℂ} (hz : z ≠ 0) {a Y : ℝ}
    (ha : 0 ≤ a) (h : a ≤ Y * m.ρ z ^ n) : a ^ 2 * wgt m n z ≤ Y ^ 2 := by
  have hρ : 0 < m.ρ z ^ n := pow_pos (m.pos z hz) n
  unfold wgt
  have e2 : m.ρ z ^ (2 * n) = (m.ρ z ^ n) ^ 2 := by ring
  rw [e2, mul_inv_le_iff₀ (by positivity)]
  calc a ^ 2 ≤ (Y * m.ρ z ^ n) ^ 2 := pow_le_pow_left₀ ha h 2
    _ = Y ^ 2 * (m.ρ z ^ n) ^ 2 := by ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
