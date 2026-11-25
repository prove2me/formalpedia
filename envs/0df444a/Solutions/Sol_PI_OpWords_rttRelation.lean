-- Prove2me | solution 1 for PI.OpWords.rttRelation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:13:59.160694+00:00
-- url     : https://prove2.me/submissions/da631bc0-2b8d-4256-a8ac-4a78df614741

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PolarizationBihomogeneous
import Theorems.Thm_PI_OpWords_rop_apply_eq
import Theorems.Thm_PI_OpWords_pderiv_inl_tt
import Theorems.Thm_PI_OpWords_pderiv_inr_tt

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
theorem _root_.solution : RTT := by
  intro K _ _ k a b g
  rw [rop_apply_eq, rop_apply_eq]
  simp only [Derivation.leibniz, pderiv_inl_tt, pderiv_inr_tt, smul_eq_mul]
  ring
end PI.OpWords
