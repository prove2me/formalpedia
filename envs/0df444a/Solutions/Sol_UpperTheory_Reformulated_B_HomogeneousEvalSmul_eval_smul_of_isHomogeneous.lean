-- Prove2me | solution 1 for UpperTheory.Reformulated.B.HomogeneousEvalSmul.eval_smul_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:01.264201+00:00
-- url     : https://prove2.me/submissions/83cb3754-525d-44d3-a888-b5e5f5b9e4e6

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalSmulOfIsHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.HomogeneousEvalSmul
theorem _root_.solution :
    ∀ {σ : Type} [Fintype σ] {h : MvPolynomial σ ℂ} {d : ℕ},
      h.IsHomogeneous d →
        ∀ (t : ℂ) (v : σ → ℂ),
          (MvPolynomial.eval (t • v) : MvPolynomial σ ℂ → ℂ) h = t ^ d * (MvPolynomial.eval v : MvPolynomial σ ℂ → ℂ) h := by
  intro σ _ h d hh t v
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have h1 := hh (MvPolynomial.mem_support_iff.mp hm)
    rw [← h1, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring
end UpperTheory.Reformulated.B.HomogeneousEvalSmul
