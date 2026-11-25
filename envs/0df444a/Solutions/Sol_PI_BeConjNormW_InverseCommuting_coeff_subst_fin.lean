-- Prove2me | solution 1 for PI.BeConjNormW.InverseCommuting.coeff_subst_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:37:10.381253+00:00
-- url     : https://prove2.me/submissions/d1f10973-fbc0-4dd4-a8c2-50bb5140d729

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_MemIntegerRingIffNormLeOne
import Theorems.Thm_PI_BeConjNormW_InverseCommuting_coeff_pow_of_lt

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
open PI.BeConjNormW.InverseCommuting
variable {p : ℕ} [Fact p.Prime]
namespace PI.BeConjNormW.InverseCommuting
theorem _root_.solution {f g : PowerSeries ℂ_[p]} (hf0 : constantCoeff f = 0) (n : ℕ) :
    coeff n (subst f g) = ∑ k ∈ Finset.range (n + 1), coeff k g * coeff n (f ^ k) := by
  have hs : HasSubst f := by
    first
    | exact HasSubst.of_constantCoeff_zero' hf0
    | exact HasSubst.of_constantCoeff_zero hf0
  have h1 : coeff n (subst f g) = ∑ᶠ k : ℕ, coeff k g * coeff n (f ^ k) := by
    first
    | exact (coeff_subst hs g (Finsupp.single () n)).trans (finsum_congr fun k => smul_eq_mul _ _)
    | (rw [coeff_subst' hs]; simp only [smul_eq_mul])
  rw [h1, finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  intro k hk
  rw [Function.mem_support] at hk
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  exact hk (by rw [coeff_pow_of_lt hf0 (by omega), mul_zero])
end PI.BeConjNormW.InverseCommuting
