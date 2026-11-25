-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.op_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:32:26.925278+00:00
-- url     : https://prove2.me/submissions/5a5ce588-d41e-440d-b700-4470d07b1dca

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ComapDomainInlAdd
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_add_f
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_zero_f
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_C
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_mul_inl
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_mul_inr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
theorem _root_.solution (u : Sym m n) : ∀ (k : Ix m n) (g : PX m n),
    op u (X k * g) = X k * op u g + op (pderiv (Sum.inr k) u) g := by
  induction u using MvPolynomial.induction_on with
  | C a => intro k g; simp [op_C, op_zero, mul_smul_comm]
  | add p q hp hq => intro k g; rw [op_add, op_add, hp, hq, map_add, op_add]; ring
  | mul_X p j hp =>
    intro k g
    rcases j with j | j
    · rw [op_mul_inl, op_mul_inl, hp, pderiv_mul, pderiv_X, op_add, op_mul_inl]
      simp only [Pi.single_apply, Sum.inl.injEq, reduceCtorEq, if_false, mul_zero, op_zero, add_zero]
      ring
    · rw [op_mul_inr, op_mul_inr, pderiv_mul, pderiv_mul, pderiv_X, pderiv_X, op_add_f, op_add, hp, op_mul_inr]
      by_cases h : j = k
      · subst h
        simp only [Pi.single_apply, if_true, mul_one, one_mul]
        ring
      · have h' : (Sum.inr k : Ix m n ⊕ Ix m n) ≠ Sum.inr j := fun e => h (Sum.inr_injective e).symm
        have e1 : ¬ (k = j) := fun e => h e.symm
        have e2 : ¬ ((Sum.inr j : Ix m n ⊕ Ix m n) = Sum.inr k) := fun e => h (Sum.inr_injective e)
        simp only [Pi.single_apply, e1, e2, if_false, zero_mul, mul_zero, op_zero, add_zero, op_zero_f, zero_add]
end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
