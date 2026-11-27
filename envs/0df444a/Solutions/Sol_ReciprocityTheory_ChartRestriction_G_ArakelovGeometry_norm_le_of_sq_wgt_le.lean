-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.norm_le_of_sq_wgt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:26:15.364683+00:00
-- url     : https://prove2.me/submissions/1f172154-feb9-4bc5-a0fd-50aedf21af0e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStC

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
theorem _root_.solution {m : ConeMetric ℂ (Ix κ)} {n : ℕ} {z : Ix κ → ℂ} (hz : z ≠ 0)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 * wgt m n z ≤ b) :
    a ≤ Real.sqrt b * m.ρ z ^ n := by
  have hρ : 0 < m.ρ z := m.pos z hz
  have hP : 0 < m.ρ z ^ n := pow_pos hρ n
  have hw : wgt m n z = ((m.ρ z ^ n) ^ 2)⁻¹ := by
    unfold wgt
    rw [← pow_mul, mul_comm n 2]
  rw [hw] at h
  have hP2 : 0 < (m.ρ z ^ n) ^ 2 := pow_pos hP 2
  have h2 : a ^ 2 ≤ b * (m.ρ z ^ n) ^ 2 := by
    rwa [← div_eq_mul_inv, div_le_iff₀ hP2] at h
  calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ Real.sqrt (b * (m.ρ z ^ n) ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt b * m.ρ z ^ n := by rw [Real.sqrt_mul hb, Real.sqrt_sq hP.le]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
