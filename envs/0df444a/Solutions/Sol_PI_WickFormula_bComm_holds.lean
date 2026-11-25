-- Prove2me | solution 1 for PI.WickFormula.bComm_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:54:48.92909+00:00
-- url     : https://prove2.me/submissions/e8773ee9-d035-4e04-ad95-f690b699bca3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_LprodAddSmul
import Theorems.Thm_PI_WickFormula_b_mul_ordEval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula
namespace PI.WickFormula
theorem _root_.solution : BComm := by
  intro k AA M _ _ _ _ _ r s a b a' b' κ σ₀ H i R
  rw [← mul_smul, b_mul_ordEval H i R, add_smul, mul_smul, H.h5 i, smul_zero, zero_add]
end PI.WickFormula
