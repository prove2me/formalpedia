-- Prove2me | solution 1 for PI.WickFormula.ordX_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:40:42.4848+00:00
-- url     : https://prove2.me/submissions/248b0b5a-c9af-4e3b-b55c-df8a622e7c7b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf
import Theorems.Thm_PI_WickFormula_lprod_bump
import Theorems.Thm_PI_WickFormula_ordEval_monomial

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
theorem _root_.solution : OrdX := by
  intro k AA _ _ _ r s a a' ha i R
  refine MvPolynomial.induction_on' R (fun m c => ?_) (fun p q hp hq => ?_)
  · have hX : (X (Sum.inl i) : MvPolynomial (Fin r ⊕ Fin s) k) * monomial m c
        = monomial (m + Finsupp.single (Sum.inl i) 1) c := by
      rw [X, monomial_mul, one_mul, add_comm]
    rw [hX, ordEval_monomial, ordEval_monomial, mul_smul_comm]
    congr 1
    unfold omon
    have hb := lprod_bump a ha (fun j => m (Sum.inl j))
      (fun j => (m + Finsupp.single (Sum.inl i) 1 : Fin r ⊕ Fin s →₀ ℕ) (Sum.inl j)) i
      (by simp) (fun i' hi' => by simp [Finsupp.single_apply, Ne.symm hi'])
    rw [hb, mul_assoc]
    simp [Finsupp.single_apply]
  · rw [mul_add, ordEval_add, ordEval_add, hp, hq, mul_add]
end PI.WickFormula
