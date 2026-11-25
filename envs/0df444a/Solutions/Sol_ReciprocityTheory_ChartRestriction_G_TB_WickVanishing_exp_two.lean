-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:40:34.446904+00:00
-- url     : https://prove2.me/submissions/8d9e3f2b-f871-49fb-bf89-6435bc9e3857

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_fin_two_finsupp_eq_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_X_add_X_pow

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
theorem _root_.solution :
    PowerSeries.subst ((X 0 : MvPowerSeries (Fin 2) k) + X 1) (PowerSeries.exp k) =
      PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) *
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) := by
  have hX : ∀ i : Fin 2, ∀ d : Fin 2 →₀ ℕ,
      MvPowerSeries.coeff d (PowerSeries.subst (X i : MvPowerSeries (Fin 2) k) (PowerSeries.exp k)) =
        if d = Finsupp.single i (d i) then algebraMap ℚ k (1 / (d i).factorial) else 0 := by
    intro i d
    rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.X i), finsum_eq_single _ (d i)]
    · rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, PowerSeries.coeff_exp]
      split_ifs <;> simp
    · intro m hm
      rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, if_neg, smul_zero]
      intro h; apply hm; rw [h]; simp
  ext e
  rw [MvPowerSeries.coeff_mul,
    Finset.sum_eq_single (Finsupp.single 0 (e 0), Finsupp.single 1 (e 1))]
  · rw [hX, hX, if_pos (by simp), if_pos (by simp)]
    rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)),
      finsum_eq_single _ (e 0 + e 1)]
    · rw [coeff_X_add_X_pow, if_pos rfl, PowerSeries.coeff_exp]
      simp only [Finsupp.single_eq_same, smul_eq_mul]
      rw [← map_natCast (algebraMap ℚ k), ← map_mul, ← map_mul]
      congr 1
      have hf0 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right (e 0) (e 1))
      rw [Nat.add_sub_cancel_left] at hf0
      have hf : (((e 0 + e 1).choose (e 0) : ℕ) : ℚ) * (e 0).factorial * (e 1).factorial =
          (e 0 + e 1).factorial := by exact_mod_cast hf0
      have ha : ((e 0).factorial : ℚ) ≠ 0 := by positivity
      have hb : ((e 1).factorial : ℚ) ≠ 0 := by positivity
      have hc : (((e 0 + e 1).choose (e 0) : ℕ) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos (Nat.le_add_right _ _)).ne'
      rw [← hf]
      field_simp
    · intro m hm
      rw [coeff_X_add_X_pow, if_neg (Ne.symm hm), smul_zero]
  · rintro ⟨p, q⟩ hpq' hne
    have hpq : p + q = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hpq'
    dsimp only
    rw [hX, hX]
    by_cases hp : p = Finsupp.single 0 (p 0)
    · by_cases hq : q = Finsupp.single 1 (q 1)
      · exfalso; apply hne
        have h0 : p 0 = e 0 := by rw [← hpq, hp, hq]; simp
        have h1 : q 1 = e 1 := by rw [← hpq, hp, hq]; simp
        rw [hp, hq, h0, h1]
      · rw [if_neg hq, mul_zero]
    · rw [if_neg hp, zero_mul]
  · intro h; exfalso; apply h
    exact Finset.HasAntidiagonal.mem_antidiagonal.mpr ((fin_two_finsupp_eq_iff e (e 0) (e 1)).2 ⟨rfl, rfl⟩).symm
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
