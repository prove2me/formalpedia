-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_log_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:33:18.800721+00:00
-- url     : https://prove2.me/submissions/46c4f448-5322-45ac-afcd-c357558138da

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_constantCoeff_psubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_constantCoeff_exp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_natCast_mul_eq_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open MvPowerSeries
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
section Two
variable (k : Type) [CommRing k] [Algebra ℚ k]
end Two
section General
variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}
end General
section Inj
variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}
private theorem one_add_X_mul_derivative_log_eq_one :
    (1 + PowerSeries.X) * PowerSeries.derivative k (PowerSeries.log k) = 1 := by
  have hD : ∀ n : ℕ,
      PowerSeries.coeff n (PowerSeries.derivative k (PowerSeries.log k)) = (-1 : k) ^ n := by
    intro n
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_log, if_neg (Nat.succ_ne_zero n)]
    have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
    rw [show ((n : k) + 1) = algebraMap ℚ k ((n : ℚ) + 1) by simp, ← map_mul]
    rw [show ((-1 : ℚ) ^ (n + 1 + 1) / ((n + 1 : ℕ) : ℚ)) * ((n : ℚ) + 1) = (-1) ^ n by
      push_cast; rw [div_mul_cancel₀ _ hn]; ring]
    simp
  ext n
  rw [add_mul, one_mul, map_add]
  rcases n with _ | n
  · simp [hD, PowerSeries.coeff_one]
  · rw [PowerSeries.coeff_succ_X_mul, hD, hD, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n)]
    ring
private theorem constantCoeff_log_eq_zero_wick_vanishing : PowerSeries.constantCoeff (PowerSeries.log k) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_log]
  simp
end Inj
section Log
variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}
private theorem eq_zero_of_one_add_X_mul_derivative_eq_self' (H : PowerSeries k) (h0 : PowerSeries.constantCoeff H = 0)
    (h : (1 + PowerSeries.X) * PowerSeries.derivative k H = H) : H = 0 := by
  have hc : ∀ n, PowerSeries.coeff n H = 0 := by
    intro n
    induction n with
    | zero => rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact h0
    | succ n ih =>
      have h1 := congrArg (PowerSeries.coeff n) h
      have hX : PowerSeries.coeff n (PowerSeries.X * PowerSeries.derivative k H) = 0 := by
        rcases n with _ | m
        · simp
        · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, ih, zero_mul]
      rw [add_mul, one_mul, map_add, hX, add_zero, PowerSeries.coeff_derivative, ih] at h1
      have h2 : ((n + 1 : ℕ) : k) * PowerSeries.coeff (n + 1) H = 0 := by
        rw [mul_comm]; push_cast; exact h1
      exact natCast_mul_eq_zero (Nat.succ_ne_zero n) h2
  ext n
  simp [hc n]
end Log
section Props
end Props
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution : PowerSeries.subst (PowerSeries.log k) (PowerSeries.exp k) = 1 + PowerSeries.X := by
  have hL : PowerSeries.HasSubst (PowerSeries.log k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' constantCoeff_log_eq_zero_wick_vanishing
  have hD : PowerSeries.derivative k (PowerSeries.subst (PowerSeries.log k) (PowerSeries.exp k)) =
      PowerSeries.subst (PowerSeries.log k) (PowerSeries.exp k) *
        PowerSeries.derivative k (PowerSeries.log k) := by
    rw [PowerSeries.derivative_subst hL, PowerSeries.derivative_exp]
  have hE0 : PowerSeries.constantCoeff
      (PowerSeries.subst (PowerSeries.log k) (PowerSeries.exp k)) = 1 := by
    have h1 := constantCoeff_psubst (σ := Unit) (a := PowerSeries.log k) constantCoeff_log_eq_zero_wick_vanishing (PowerSeries.exp k)
    rw [PowerSeries.constantCoeff_exp] at h1
    exact h1
  have hH := eq_zero_of_one_add_X_mul_derivative_eq_self' (PowerSeries.subst (PowerSeries.log k) (PowerSeries.exp k) -
    (1 + PowerSeries.X)) (by simp [hE0]) (by
      rw [map_sub, map_add, hD, PowerSeries.derivative_X, Derivation.map_one_eq_zero, zero_add]
      linear_combination (PowerSeries.subst (PowerSeries.log k) (PowerSeries.exp k)) * one_add_X_mul_derivative_log_eq_one (k := k))
  exact sub_eq_zero.mp hH
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
