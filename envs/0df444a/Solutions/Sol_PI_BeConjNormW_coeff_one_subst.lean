-- Prove2me | solution 1 for PI.BeConjNormW.coeff_one_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:34:41.762588+00:00
-- url     : https://prove2.me/submissions/4b67c952-7c11-4668-a4bd-648d4ecf235a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BeConjNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_BeConjNormOfIntInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BeConjNormW
open PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula
variable {p : ℕ} [Fact p.Prime]
namespace PI.BeConjNormW
theorem _root_.solution (a f : PowerSeries ℂ_[p]) (ha : PowerSeries.constantCoeff a = 0)
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff 1 (PowerSeries.subst a f : PowerSeries ℂ_[p]) = PowerSeries.coeff 1 f * PowerSeries.coeff 1 a := by
  have hs : PowerSeries.HasSubst a := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero' ha
    | exact PowerSeries.HasSubst.of_constantCoeff_zero ha
  have h1 : PowerSeries.coeff 1 (PowerSeries.subst a f : PowerSeries ℂ_[p]) =
      ∑ᶠ k : ℕ, PowerSeries.coeff k f * PowerSeries.coeff 1 (a ^ k) :=
    (PowerSeries.coeff_subst hs f (Finsupp.single () 1)).trans (finsum_congr fun k => smul_eq_mul _ _)
  have hz : ∀ k, 2 ≤ k → PowerSeries.coeff 1 (a ^ k) = 0 := by
    intro k hk
    obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr ha
    rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  rw [h1, finsum_eq_sum_of_support_subset _ (s := Finset.range 2)]
  · rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_mul, zero_add]
  · intro k hk
    rw [Function.mem_support] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hk (by rw [hz k (by omega), mul_zero])
end PI.BeConjNormW
