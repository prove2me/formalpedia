-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.bwp_eval_smul_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:01:17.183545+00:00
-- url     : https://prove2.me/submissions/7fbebb5c-ba39-4b9a-a3b4-535deae57562

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyA
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyC

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
theorem _root_.solution {σ : Type*} {φ : MvPolynomial σ ℂ} {d : ℕ}
    (hφ : φ.IsHomogeneous d) (t : ℂ) (z : σ → ℂ) :
    MvPolynomial.eval (t • z) φ = t ^ d * MvPolynomial.eval z φ := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = d := by
    have h := hφ (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp_rw [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    hdeg]
  ring
end ReciprocityTheory.MultiplicativeHeights
