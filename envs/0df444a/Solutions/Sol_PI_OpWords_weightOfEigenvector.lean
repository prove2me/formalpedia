-- Prove2me | solution 1 for PI.OpWords.weightOfEigenvector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:07:32.804719+00:00
-- url     : https://prove2.me/submissions/674bde2a-a1fb-4274-ac3e-b9b6b85f724b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PolarizationBihomogeneous
import Theorems.Thm_PI_OpWords_rop_apply_eq
import Theorems.Thm_PI_OpWords_coeff_X_pderiv_self

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
theorem _root_.solution : WtOfEig := by
  intro K _ _ k a w f h m hm
  have h1 := congrArg (coeff m) h
  rw [rop_apply_eq, coeff_sub, coeff_X_pderiv_self, coeff_X_pderiv_self, coeff_smul] at h1
  have hc : coeff m f ≠ 0 := MvPolynomial.mem_support_iff.1 hm
  have h2 : (((m (Sum.inl a) : ℤ) - m (Sum.inr a) : ℤ) : K) = (w : K) := by
    apply mul_left_cancel₀ hc
    push_cast
    linear_combination h1
  exact_mod_cast h2
end PI.OpWords
