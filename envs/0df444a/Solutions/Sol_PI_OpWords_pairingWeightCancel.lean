-- Prove2me | solution 1 for PI.OpWords.pairingWeightCancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:08:36.736071+00:00
-- url     : https://prove2.me/submissions/7cf5562e-a0b0-4386-a51d-851b9519db88

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PolarizationBihomogeneous
import Theorems.Thm_PI_OpWords_weight_va
import Theorems.Thm_PI_OpWords_tt_va
import Theorems.Thm_PI_OpWords_comp_mul_zero
import Theorems.Thm_PI_OpWords_tt_ne_zero

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
theorem _root_.solution : TTWt := by
  intro K _ _ k c g h m hm a
  by_contra hlt
  push_neg at hlt
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = (m (Sum.inl a) : ℤ) - m (Sum.inr a) := ⟨_, rfl⟩
  have hwm : weight (va k a) m = n := by rw [weight_va, hn]
  have hk : 0 < k := Fin.pos a
  have hcomp : weightedHomogeneousComponent (va k a) n g ≠ 0 := by
    intro h0
    have h3 := congrArg (coeff m) h0
    rw [coeff_weightedHomogeneousComponent, if_pos hwm] at h3
    exact (MvPolynomial.mem_support_iff.1 hm) (by simpa using h3)
  have hprod : weightedHomogeneousComponent (va k a) n (tt K k * g) ≠ 0 := by
    rw [comp_mul_zero (va k a) (tt_va K k a) n g]
    exact mul_ne_zero (tt_ne_zero K k hk) hcomp
  apply hprod
  ext m'
  rw [coeff_weightedHomogeneousComponent, coeff_zero]
  split_ifs with hw
  · by_contra hne
    have h4 := h m' (MvPolynomial.mem_support_iff.2 hne) a
    rw [weight_va] at hw
    omega
  · rfl
end PI.OpWords
