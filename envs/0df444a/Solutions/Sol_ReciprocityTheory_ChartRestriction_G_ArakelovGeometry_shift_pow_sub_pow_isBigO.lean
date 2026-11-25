-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.shift_pow_sub_pow_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:43:38.20697+00:00
-- url     : https://prove2.me/submissions/2aafba6e-b886-44db-96e9-4b8dd068aa8c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ChooseLePowDivFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Module Filter Asymptotics
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (D : ℕ) (a : ℝ) :
    (fun n : ℕ => ((n : ℝ) + a) ^ D - (n : ℝ) ^ D) =O[atTop] fun n : ℕ => (n : ℝ) ^ D / (n : ℝ) := by
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · simp
    exact Asymptotics.isBigO_zero _ _
  have key : (fun n : ℕ => ((n : ℝ) + a) ^ D - (n : ℝ) ^ D) =
      ∑ i ∈ Finset.range D, fun n : ℕ => (n : ℝ) ^ i * a ^ (D - i) * (D.choose i : ℝ) := by
    funext n
    rw [Finset.sum_apply, add_pow, Finset.sum_range_succ]
    simp
  rw [key]
  refine Asymptotics.IsBigO.sum fun i hi => ?_
  have hi' : i + 1 ≤ D := Finset.mem_range.1 hi
  refine Asymptotics.IsBigO.of_bound (|a| ^ (D - i) * (D.choose i : ℝ)) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  have hdiv : (n : ℝ) ^ D / n = (n : ℝ) ^ (D - 1) := by
    rw [div_eq_iff hpos.ne', ← pow_succ, Nat.sub_add_cancel hD]
  rw [hdiv]
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, Nat.abs_cast]
  have hle : (n : ℝ) ^ i ≤ (n : ℝ) ^ (D - 1) := pow_le_pow_right₀ hn' (by omega)
  have hc : 0 ≤ |a| ^ (D - i) * (D.choose i : ℝ) := by positivity
  nlinarith
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
