-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.eval_smul_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:01:49.070408+00:00
-- url     : https://prove2.me/submissions/99d84da7-ee06-40f2-938d-dec6b434fd83

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_LogNormEvalZeroLeCircleAverage

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
open Polynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {σ : Type*} {f : MvPolynomial σ ℂ} {a : ℕ}
    (hf : f.IsHomogeneous a) (c : ℂ) (x : σ → ℂ) :
    MvPolynomial.eval (fun i => c * x i) f = c ^ a * MvPolynomial.eval x f := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = a := by
    have h := hf (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring
end ReciprocityTheory.MultiplicativeHeights
