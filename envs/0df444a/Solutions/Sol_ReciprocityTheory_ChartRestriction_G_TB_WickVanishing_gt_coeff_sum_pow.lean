-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_coeff_sum_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:33:18.791454+00:00
-- url     : https://prove2.me/submissions/57f9ca1a-0dc4-4d6c-902c-b83a3302fd0b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_single_add

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable (A : Type) [CommRing A] [Algebra ℚ A]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution (n : ℕ) (e : Fin 2 →₀ ℕ) :
    coeff e (((X 0 : MvPowerSeries (Fin 2) A) + X 1) ^ n) =
      if e 0 + e 1 = n then ((n.choose (e 0) : ℕ) : A) else 0 := by
  have hterm : ∀ m, coeff e ((X 0 : MvPowerSeries (Fin 2) A) ^ m * X 1 ^ (n - m) *
      ((n.choose m : ℕ) : MvPowerSeries (Fin 2) A)) =
      if e = single 0 m + single 1 (n - m) then ((n.choose m : ℕ) : A) else 0 := by
    intro m
    rw [mul_comm _ ((n.choose m : ℕ) : MvPowerSeries (Fin 2) A), ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul,
      MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial,
      MvPowerSeries.coeff_monomial]
    split_ifs <;> simp
  rw [add_pow, map_sum]
  simp_rw [hterm]
  rw [Finset.sum_eq_single (e 0)]
  · by_cases h : e 0 + e 1 = n
    · rw [if_pos h, if_pos]
      rw [show n - e 0 = e 1 by omega]
      exact gt_single_add e
    · rw [if_neg h]
      split_ifs with he
      · have h1 : e 1 = n - e 0 := by simpa using DFunLike.congr_fun he 1
        have hlt : n < e 0 := by omega
        rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero]
      · rfl
  · intro b _ hb
    rw [if_neg]
    intro he
    apply hb
    have h0 : e 0 = b := by simpa using DFunLike.congr_fun he 0
    exact h0.symm
  · intro hn
    have hlt : n < e 0 := by
      simp only [Finset.mem_range, not_lt] at hn
      omega
    split_ifs
    · rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero]
    · rfl
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
