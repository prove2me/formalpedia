-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_X_add_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:32:50.630938+00:00
-- url     : https://prove2.me/submissions/e7acde4f-57a4-457e-b3fa-c01d8f4cfc39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_fin_two_finsupp_eq_iff

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable (k : Type) [CommRing k] [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution (e : Fin 2 →₀ ℕ) (n : ℕ) :
    MvPowerSeries.coeff e (((X 0 : MvPowerSeries (Fin 2) k) + X 1) ^ n) =
      if e 0 + e 1 = n then (n.choose (e 0) : k) else 0 := by
  rw [add_pow, map_sum]
  have hterm : ∀ m ∈ Finset.range (n + 1),
      MvPowerSeries.coeff e ((X 0 : MvPowerSeries (Fin 2) k) ^ m * X 1 ^ (n - m) *
        (n.choose m : MvPowerSeries (Fin 2) k)) =
        if e 0 = m ∧ e 1 = n - m then (n.choose m : k) else 0 := by
    intro m _
    rw [mul_comm, ← nsmul_eq_mul, map_nsmul, MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq,
      MvPowerSeries.monomial_mul_monomial, one_mul, MvPowerSeries.coeff_monomial]
    by_cases h : e 0 = m ∧ e 1 = n - m
    · rw [if_pos h, if_pos ((fin_two_finsupp_eq_iff e m (n - m)).2 h)]; simp
    · rw [if_neg h, if_neg (fun h' => h ((fin_two_finsupp_eq_iff e m (n - m)).1 h'))]; simp
  rw [Finset.sum_congr rfl hterm]
  split_ifs with hn
  · rw [Finset.sum_eq_single (e 0)]
    · rw [if_pos ⟨rfl, by omega⟩]
    · intro m _ hm
      rw [if_neg (fun h => hm h.1.symm)]
    · intro h
      exfalso; exact h (Finset.mem_range.mpr (by omega))
  · apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_range] at hm
    rw [if_neg (fun h => hn (by omega))]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
