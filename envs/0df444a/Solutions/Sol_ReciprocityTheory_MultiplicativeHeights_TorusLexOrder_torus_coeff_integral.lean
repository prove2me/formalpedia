-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.TorusLexOrder.torus_coeff_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:56:53.602563+00:00
-- url     : https://prove2.me/submissions/1f1396c5-c2ae-401f-b71f-95e187d0c0d7

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLexB
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLexC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_integrable_mono_term
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_eval_torus
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_torus_orth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
open MeasureTheory ComplexConjugate
namespace ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
theorem _root_.solution {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) (s : ι →₀ ℕ) :
    ∫ θ, MvPolynomial.eval (torusPoint θ) f * conj (torusMono θ s) ∂(torusProb ι) =
      f.coeff s := by
  simp_rw [eval_torus, Finset.sum_mul]
  rw [integral_finset_sum _ (fun t _ => by
    simpa [mul_assoc] using (integrable_mono_term t s).const_mul (f.coeff t))]
  simp_rw [mul_assoc, integral_const_mul, torus_orth, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (MvPolynomial.notMem_support_iff.mp h).symm
end ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
