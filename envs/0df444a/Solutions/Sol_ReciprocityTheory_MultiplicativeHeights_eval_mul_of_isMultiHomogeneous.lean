-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.eval_mul_of_isMultiHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:45.219741+00:00
-- url     : https://prove2.me/submissions/82ef05cc-59a0-4562-8eda-d8f319954236

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {B n : ℕ} {a : Fin B → ℕ} {g : MvPolynomial (Fin B × Fin n) ℂ}
    (hg : IsMultiHomogeneous a g) (c : ℂ) (z : Fin B × Fin n → ℂ) :
    eval (fun p => c * z p) g = c ^ (∑ b, a b) * eval z g := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hdeg : ∑ p, s p = ∑ b, a b := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun b _ => hg s hs b
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring
end ReciprocityTheory.MultiplicativeHeights
