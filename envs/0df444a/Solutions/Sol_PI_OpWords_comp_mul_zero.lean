-- Prove2me | solution 1 for PI.OpWords.comp_mul_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:01:35.230686+00:00
-- url     : https://prove2.me/submissions/4c0bbe94-eb9e-42c1-aaeb-b7d9fae63872

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PolarizationBihomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finsupp
noncomputable section
open PI PI.OpWords
namespace PI.OpWords
theorem _root_.solution {σ : Type} {K : Type} [Field K] (w : σ → ℤ) {φ : MvPolynomial σ K}
    (hφ : IsWeightedHomogeneous w φ 0) (n : ℤ) (ψ : MvPolynomial σ K) :
    weightedHomogeneousComponent w n (φ * ψ) = φ * weightedHomogeneousComponent w n ψ := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with hd
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases h0 : coeff x.1 φ = 0
    · simp [h0]
    · have hx0 := hφ h0
      have hsum := by simpa using hx
      have hw : weight w x.2 = n := by
        rw [← hd, ← hsum, map_add, hx0, zero_add]
      rw [if_pos hw]
  · symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases h0 : coeff x.1 φ = 0
    · simp [h0]
    · have hx0 := hφ h0
      have hsum := by simpa using hx
      have hw : weight w x.2 ≠ n := by
        rw [← hsum, map_add, hx0, zero_add] at hd
        exact hd
      rw [if_neg hw, mul_zero]
end PI.OpWords
