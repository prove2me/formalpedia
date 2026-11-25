-- Prove2me | solution 1 for PI.BeConjNormW.inverse_integral_padic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:41:24.717793+00:00
-- url     : https://prove2.me/submissions/60a15845-cd07-4cf2-961e-3dc40e84011c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_MemIntegerRingIffNormLeOne
import Theorems.Thm_PI_BeConjNormW_InverseCommuting_mem_integerRing_iff_norm_le_one
import Theorems.Thm_PI_BeConjNormW_InverseCommuting_coeff_pow_int
import Theorems.Thm_PI_BeConjNormW_InverseCommuting_coeff_pow_self
import Theorems.Thm_PI_BeConjNormW_InverseCommuting_coeff_subst_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical PowerSeries
open PI PI.BeConjNormW
open InverseCommuting
namespace PI.BeConjNormW
theorem _root_.solution : IntInv := by
  intro p _ f g hf0 hg0 h1 hf hfg n
  have key : ∀ m, coeff m g ∈ PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [coeff_zero_eq_constantCoeff_apply, hg0]
        exact zero_mem _
      · have hs := coeff_subst_fin (g := g) hf0 m
        rw [hfg, Finset.sum_range_succ, coeff_pow_self hf0] at hs
        have hrest : (∑ k ∈ Finset.range m, coeff k g * coeff m (f ^ k)) ∈
            PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p :=
          sum_mem fun k hk => mul_mem (ih k (Finset.mem_range.mp hk)) ((mem_integerRing_iff_norm_le_one _).2 (coeff_pow_int hf k m))
        have hX : coeff m (X : PowerSeries ℂ_[p]) ∈ PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p := by
          rw [coeff_X]
          split_ifs
          · exact one_mem _
          · exact zero_mem _
        have hprod : coeff m g * coeff 1 f ^ m ∈ PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p := by
          have he : coeff m g * coeff 1 f ^ m =
              coeff m (X : PowerSeries ℂ_[p]) - ∑ k ∈ Finset.range m, coeff k g * coeff m (f ^ k) := by
            rw [hs]
            ring
          rw [he]
          exact sub_mem hX hrest
        rw [mem_integerRing_iff_norm_le_one] at hprod ⊢
        rwa [norm_mul, norm_pow, h1, one_pow, mul_one] at hprod
  exact (mem_integerRing_iff_norm_le_one _).1 (key n)
end PI.BeConjNormW
