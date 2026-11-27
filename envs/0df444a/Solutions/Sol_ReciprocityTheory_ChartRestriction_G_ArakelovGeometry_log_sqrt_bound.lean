-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.log_sqrt_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:37:44.242043+00:00
-- url     : https://prove2.me/submissions/af339c5c-63b4-48e3-9912-9555868dff39

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
theorem _root_.solution (D : ℕ) {T : ℝ} (hT : 1 ≤ T) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ Real.log (Real.sqrt (T * (n : ℝ) ^ D)) ∧
      Real.log (Real.sqrt (T * (n : ℝ) ^ D)) ≤
        (1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hT0' : 0 < T := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hpos : 0 < T * (n : ℝ) ^ D := mul_pos hT0' (pow_pos hnpos D)
  have hlog : Real.log (Real.sqrt (T * (n : ℝ) ^ D)) = (1 / 2) * (Real.log T + D * Real.log n) := by
    rw [Real.log_sqrt hpos.le, Real.log_mul hT0'.ne' (pow_pos hnpos D).ne', Real.log_pow]
    ring
  have hT0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hn0 : 0 ≤ Real.log n := Real.log_nonneg hn'
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2n : Real.log 2 ≤ Real.log (n + 1) := Real.log_le_log (by norm_num) (by linarith)
  have hln : Real.log n ≤ Real.log (n + 1) := Real.log_le_log hnpos (by linarith)
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  refine ⟨?_, ?_⟩
  · rw [hlog]
    exact mul_nonneg (by norm_num) (add_nonneg hT0 (mul_nonneg hD0 hn0))
  · rw [hlog]
    have h1 : Real.log T ≤ Real.log T / Real.log 2 * Real.log (n + 1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hl2n hT0
    have h2 : (D : ℝ) * Real.log n ≤ D * Real.log (n + 1) := mul_le_mul_of_nonneg_left hln hD0
    have h3 : (1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1) =
        (1 / 2) * (Real.log T / Real.log 2 * Real.log (n + 1) + D * Real.log (n + 1)) := by ring
    rw [h3]
    linarith
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
