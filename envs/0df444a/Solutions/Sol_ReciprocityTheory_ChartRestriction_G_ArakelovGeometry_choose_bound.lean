-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.choose_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:25:21.990915+00:00
-- url     : https://prove2.me/submissions/ffb5d2b1-2ebf-4eb3-b8df-6e031c53c035

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
theorem _root_.solution (k D : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (((n + k + D).choose D : ℕ) : ℝ) ≤ ((1 + k + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D := by
  have hN : n + k + D ≤ (1 + k + D) * n := by nlinarith
  have h1 : (n + k + D).choose D ≤ (n + k + D) ^ D := Nat.choose_le_pow _ _
  have h2 : (n + k + D) ^ D ≤ ((1 + k + D) * n) ^ D := Nat.pow_le_pow_left hN D
  have h3 : (n + k + D).choose D ≤ (1 + k + D) ^ D * n ^ D := by
    rw [← mul_pow]
    exact h1.trans h2
  exact_mod_cast h3
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
