-- Prove2me | solution 1 for PI.WickFormula.add_pow_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:14:36.825802+00:00
-- url     : https://prove2.me/submissions/0a0fddf1-f997-471f-9516-ce6d298bc3fb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_LprodAddSmul

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
variable {AA : Type} [Ring AA]
namespace PI.WickFormula
theorem _root_.solution {M : Type} [AddCommGroup M] [Module AA M] (x y : AA) (w : M)
    (hxy : Commute y x) (hw : y • w = 0) (n : ℕ) : (x + y) ^ n • w = x ^ n • w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    have hyx : y • (x • w) = 0 := by rw [← mul_smul, hxy.eq, mul_smul, hw, smul_zero]
    rw [pow_succ, mul_smul, add_smul, hw, add_zero, ih (x • w) hyx, ← mul_smul, ← pow_succ]
end PI.WickFormula
