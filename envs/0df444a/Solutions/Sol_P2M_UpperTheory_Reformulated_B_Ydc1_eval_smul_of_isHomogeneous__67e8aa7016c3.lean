-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Ydc1_eval_smul_of_isHomogeneous__67e8aa7016c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:01:21.123352+00:00
-- url     : https://prove2.me/submissions/b1b0121d-b084-4cdb-803b-205f4205ea13

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalSmulOfIsHomogeneousAlt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Ydc1.eval_smul_of_isHomogeneous
theorem _root_.solution.{u_1} :
    ∀ {τ : Type u_1} {φ : MvPolynomial τ ℂ} {n : ℕ},
      φ.IsHomogeneous n →
        ∀ (c : ℂ) (w : τ → ℂ),
          (MvPolynomial.eval (c • w) : MvPolynomial τ ℂ → ℂ) φ = c ^ n * (MvPolynomial.eval w : MvPolynomial τ ℂ → ℂ) φ := by
  intro τ φ n hφ c w
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    have h := hφ (MvPolynomial.mem_support_iff.mp hd)
    rw [← h, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring
end UpperTheory.Reformulated.B.Ydc1.eval_smul_of_isHomogeneous
