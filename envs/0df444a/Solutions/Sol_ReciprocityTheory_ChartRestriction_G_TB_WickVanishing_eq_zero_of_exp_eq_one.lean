-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.eq_zero_of_exp_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:08.639804+00:00
-- url     : https://prove2.me/submissions/0e0826df-8911-4d9a-ad2f-c16f4b199789

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
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
private theorem powerSeries_subst_zero_eq_C_constantCoeff (f : PowerSeries k) :
    PowerSeries.subst (0 : MvPowerSeries σ k) f = MvPowerSeries.C (PowerSeries.constantCoeff f) := by
  classical
  ext e
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)),
    finsum_eq_single _ 0 (fun d hd => by simp [zero_pow hd])]
  by_cases he : e = 0
  · subst he; simp
  · simp only [smul_eq_mul, pow_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [MvPowerSeries.coeff_one, if_neg he, mul_zero, MvPowerSeries.coeff_C, if_neg he]
private theorem powerSeries_subst_one (a : MvPowerSeries σ k) :
    PowerSeries.subst a (1 : PowerSeries k) = 1 := by
  rw [show (1 : PowerSeries k) = PowerSeries.C (1 : k) from (map_one _).symm, PowerSeries.subst_C,
    map_one]
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
private theorem isAddTorsionFree_coeff_ring : IsAddTorsionFree k := by
  first
  | infer_instance
  | exact ⟨fun n hn a b hab => by
      have h2 : (n : k) * (a - b) = 0 := by
        simp only [nsmul_eq_mul] at hab; rw [mul_sub, hab, sub_self]
      exact sub_eq_zero.mp (natCast_mul_eq_zero hn h2)⟩
private theorem subst_exp_sub_one_log_eq_X :
    PowerSeries.subst (PowerSeries.exp k - 1) (PowerSeries.log k) = PowerSeries.X := by
  haveI := isAddTorsionFree_coeff_ring (k := k)
  have hs : PowerSeries.HasSubst (PowerSeries.exp k - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  apply PowerSeries.derivative.ext
  · rw [PowerSeries.derivative_subst hs, PowerSeries.derivative_X, map_sub,
      PowerSeries.derivative_exp, Derivation.map_one_eq_zero, sub_zero]
    have h1 := congrArg (PowerSeries.subst (PowerSeries.exp k - 1)) (one_add_X_mul_derivative_log_eq_one (k := k))
    rw [PowerSeries.subst_mul hs, PowerSeries.subst_add hs, powerSeries_subst_one, PowerSeries.subst_X hs] at h1
    linear_combination h1
  · rw [PowerSeries.constantCoeff_X]
    exact PowerSeries.constantCoeff_subst_eq_zero
      (by rw [map_sub, map_one]; exact sub_eq_zero.mpr PowerSeries.constantCoeff_exp) _ constantCoeff_log_eq_zero_wick_vanishing
private theorem subst_log_subst_exp_sub_one_eq_self {a : MvPowerSeries σ k} (ha : constantCoeff a = 0) :
    PowerSeries.subst (PowerSeries.subst a (PowerSeries.exp k) - 1) (PowerSeries.log k) = a := by
  have ha' : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have h1 : PowerSeries.subst a (PowerSeries.exp k) - 1 =
      PowerSeries.subst a (PowerSeries.exp k - 1) := by
    have h2 := PowerSeries.subst_add ha' (PowerSeries.exp k - 1) 1
    rw [sub_add_cancel, powerSeries_subst_one] at h2
    rw [h2]; ring
  have hs : PowerSeries.HasSubst (PowerSeries.exp k - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  rw [h1, ← PowerSeries.subst_comp_subst_apply hs ha', subst_exp_sub_one_log_eq_X, PowerSeries.subst_X ha']
end Inj
section Log
variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}
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
theorem _root_.solution {c : MvPowerSeries σ k} (hc : constantCoeff c = 0)
    (h : PowerSeries.subst c (PowerSeries.exp k) = 1) : c = 0 := by
  have h1 := subst_log_subst_exp_sub_one_eq_self hc
  rw [h, sub_self, powerSeries_subst_zero_eq_C_constantCoeff, constantCoeff_log_eq_zero_wick_vanishing, map_zero] at h1
  exact h1.symm
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
