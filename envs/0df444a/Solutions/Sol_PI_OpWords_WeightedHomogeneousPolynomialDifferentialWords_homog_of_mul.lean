-- Prove2me | solution 1 for PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.homog_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:00:37.284369+00:00
-- url     : https://prove2.me/submissions/d72784ff-2b51-4830-beef-1322d0ffb7d0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_IsWeightedHomogeneousPairingLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
theorem _root_.solution {σ : Type} (w : σ → ℕ) {s g : MvPolynomial σ K} {n : ℕ}
    (hs : IsWeightedHomogeneous w s 1) (hs0 : s ≠ 0)
    (h : IsWeightedHomogeneous w (s * g) (1 + n)) : IsWeightedHomogeneous w g n := by
  classical
  have hA : ∀ j, weightedHomogeneousComponent w (1 + j) (s * g) = s * weightedHomogeneousComponent w j g := by
    intro j
    ext d
    rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
    split_ifs with hd
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [coeff_weightedHomogeneousComponent]
      by_cases h0 : coeff x.1 s = 0
      · simp [h0]
      · have hx0 := hs h0
        have hsum : x.1 + x.2 = d := by simpa using hx
        have hw : Finsupp.weight w x.2 = j := by
          rw [← hsum, map_add, hx0] at hd
          omega
        rw [if_pos hw]
    · symm
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [coeff_weightedHomogeneousComponent]
      by_cases h0 : coeff x.1 s = 0
      · simp [h0]
      · have hx0 := hs h0
        have hsum : x.1 + x.2 = d := by simpa using hx
        have hw : Finsupp.weight w x.2 ≠ j := by
          rw [← hsum, map_add, hx0] at hd
          omega
        rw [if_neg hw, mul_zero]
  intro m hm
  by_contra hne
  have hc : weightedHomogeneousComponent w (Finsupp.weight w m) g ≠ 0 := by
    intro h0
    have h3 := congrArg (coeff m) h0
    rw [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at h3
    exact hm h3
  apply hc
  have h4 : s * weightedHomogeneousComponent w (Finsupp.weight w m) g = 0 := by
    rw [← hA]
    ext d
    rw [coeff_weightedHomogeneousComponent, coeff_zero]
    split_ifs with hd
    · by_contra hne2
      have h5 := h hne2
      omega
    · rfl
  exact (mul_eq_zero.1 h4).resolve_left hs0
end PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
