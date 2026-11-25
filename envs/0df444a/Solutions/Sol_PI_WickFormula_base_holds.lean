-- Prove2me | solution 1 for PI.WickFormula.base_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:42:17.388311+00:00
-- url     : https://prove2.me/submissions/5a4cae87-c64a-457e-a4ca-1e98efdbc53a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_LprodAddSmul
import Theorems.Thm_PI_WickFormula_lprod_of_zero
import Theorems.Thm_PI_WickFormula_lprod_add_smul

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
theorem _root_.solution : Base := by
  intro k AA M _ _ _ _ _ r s a b a' b' κ σ₀ H Q hQ
  unfold ordEval
  rw [Finset.sum_smul, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro m hm
  have key : (lprod (a + b) (fun i => m (Sum.inl i)) * lprod (a' + b') (fun j => m (Sum.inr j))) • σ₀ =
      (lprod a (fun i => m (Sum.inl i)) * lprod a' (fun j => m (Sum.inr j))) • σ₀ := by
    rw [lprod_of_zero _ _ (fun i => hQ m hm i), lprod_of_zero _ _ (fun i => hQ m hm i), one_mul, one_mul]
    exact lprod_add_smul a' b' _ σ₀ (fun i j => (H.h2 j i).2.1.symm) H.h6
  simp only [lprod] at key
  simp only [mul_smul] at key
  simp only [Algebra.smul_def, mul_smul]
  rw [key]
end PI.WickFormula
