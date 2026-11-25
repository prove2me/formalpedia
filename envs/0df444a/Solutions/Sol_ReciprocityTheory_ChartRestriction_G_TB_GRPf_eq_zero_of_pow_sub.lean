-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GRPf.eq_zero_of_pow_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:31:16.024273+00:00
-- url     : https://prove2.me/submissions/3bc98654-b848-482b-9fbb-1d06f0e0d86e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeRatio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GRPf
variable {O k T : Type} [CommRing O] [StarRing O] [CommRing k] [Algebra ℚ k] [Fintype T] {rk : T → ℕ}
  (χ : T → O →+* k)
namespace ReciprocityTheory.ChartRestriction.G.TB.GRPf
theorem _root_.solution {n : ℕ} (hn : n ≠ 2) {x : k} (h : ((2 : k) ^ n - 4) * x = 0) : x = 0 := by
  have hq : ((2 : ℚ) ^ n - 4) ≠ 0 := by
    intro h0
    have h4 : (2 : ℚ) ^ n = 2 ^ 2 := by linarith
    exact hn (Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h4))
  have e : algebraMap ℚ k ((2 : ℚ) ^ n - 4) * x = 0 := by
    rw [map_sub, map_pow, map_ofNat (algebraMap ℚ k) 2, map_ofNat (algebraMap ℚ k) 4]
    exact h
  calc x = algebraMap ℚ k (((2 : ℚ) ^ n - 4)⁻¹ * ((2 : ℚ) ^ n - 4)) * x := by
        rw [inv_mul_cancel₀ hq, map_one, one_mul]
    _ = algebraMap ℚ k (((2 : ℚ) ^ n - 4)⁻¹) * (algebraMap ℚ k ((2 : ℚ) ^ n - 4) * x) := by
        rw [map_mul, mul_assoc]
    _ = 0 := by rw [e, mul_zero]
end ReciprocityTheory.ChartRestriction.G.TB.GRPf
