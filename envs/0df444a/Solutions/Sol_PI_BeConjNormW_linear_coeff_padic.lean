-- Prove2me | solution 1 for PI.BeConjNormW.linear_coeff_padic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:09.58441+00:00
-- url     : https://prove2.me/submissions/65038d29-3bfb-4bc7-b4b2-c5c4b944e0fb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BeConjNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_BeConjNormOfIntInv
import Theorems.Thm_PI_BeConjNormW_coeff_one_subst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Classical
namespace PI.BeConjNormW
open PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula
variable {p : ℕ} [Fact p.Prime]
private theorem coeff_zero_subst_of_constantCoeff_eq_zero (a f : PowerSeries ℂ_[p]) (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.coeff 0 (PowerSeries.subst a f : PowerSeries ℂ_[p]) = PowerSeries.coeff 0 f := by
  have hs : PowerSeries.HasSubst a := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero' ha
    | exact PowerSeries.HasSubst.of_constantCoeff_zero ha
  have h1 : PowerSeries.coeff 0 (PowerSeries.subst a f : PowerSeries ℂ_[p]) =
      ∑ᶠ k : ℕ, PowerSeries.coeff k f * PowerSeries.coeff 0 (a ^ k) :=
    (PowerSeries.coeff_subst hs f (Finsupp.single () 0)).trans (finsum_congr fun k => smul_eq_mul _ _)
  rw [h1, finsum_eq_sum_of_support_subset _ (s := Finset.range 1)]
  · simp
  · intro k hk
    rw [Function.mem_support] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hk
    obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr ha
    rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega), mul_zero]
end PI.BeConjNormW
end
end

set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BeConjNormW
open PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula
variable {p : ℕ} [Fact p.Prime]
namespace PI.BeConjNormW
theorem _root_.solution : LinCoeff := by
  intro q _ l ex hex hle c
  have hl0 : PowerSeries.constantCoeff l = 0 := by
    have h := coeff_zero_subst_of_constantCoeff_eq_zero ex l hex
    rw [hle, PowerSeries.coeff_zero_X, PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
    exact h.symm
  have hprod : PowerSeries.coeff 1 l * PowerSeries.coeff 1 ex = 1 := by
    have h := coeff_one_subst ex l hex hl0
    rw [hle, PowerSeries.coeff_one_X] at h
    exact h.symm
  have hX0 : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries ℂ_[q]) = 0 := PowerSeries.constantCoeff_X
  have hsX0 : PowerSeries.constantCoeff (PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[q]) l : PowerSeries ℂ_[q]) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_subst_of_constantCoeff_eq_zero _ _ hX0,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hl0]
  have hsX1 : PowerSeries.coeff 1 (PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[q]) l : PowerSeries ℂ_[q]) =
      PowerSeries.coeff 1 l := by
    rw [coeff_one_subst _ _ hX0 hl0, PowerSeries.coeff_one_X, mul_one]
  have hc0 : PowerSeries.constantCoeff
      (PowerSeries.C c * PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[q]) l : PowerSeries ℂ_[q]) = 0 := by
    rw [map_mul, hsX0, mul_zero]
  have key := coeff_one_subst
    (PowerSeries.C c * PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[q]) l : PowerSeries ℂ_[q]) ex hc0 hex
  rw [PowerSeries.coeff_C_mul, hsX1] at key
  show PowerSeries.coeff 1 (PowerSeries.subst
    (PowerSeries.C c * PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[q]) l : PowerSeries ℂ_[q]) ex : PowerSeries ℂ_[q]) = c
  rw [key]
  linear_combination c * hprod
end PI.BeConjNormW
