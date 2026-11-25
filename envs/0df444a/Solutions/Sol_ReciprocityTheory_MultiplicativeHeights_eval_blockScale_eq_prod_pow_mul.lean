-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.eval_blockScale_eq_prod_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:01:45.700408+00:00
-- url     : https://prove2.me/submissions/731fd170-fa9f-446a-9559-e4490b116a88

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {B n : ℕ} (a : Fin B → ℕ) (F : MvPolynomial (Fin B × Fin n) ℂ)
    (hF : IsMultiHomogeneous a F) (r : Fin B → ℂ) (x : Fin B × Fin n → ℂ) :
    MvPolynomial.eval (fun p => r p.1 * x p) F = (∏ b, r b ^ a b) * MvPolynomial.eval x F := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h1 : ∏ p, (r p.1 * x p) ^ s p = (∏ b, r b ^ a b) * ∏ p, x p ^ s p := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun b _ => ?_
    show ∏ j, r b ^ s (b, j) = r b ^ a b
    rw [Finset.prod_pow_eq_pow_sum, hF s hs b]
  rw [h1]
  ring
end ReciprocityTheory.MultiplicativeHeights
