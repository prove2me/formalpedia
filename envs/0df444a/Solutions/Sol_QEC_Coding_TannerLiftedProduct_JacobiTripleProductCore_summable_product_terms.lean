-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_product_terms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:38:06.340506+00:00
-- url     : https://prove2.me/submissions/0ef96a40-2786-49fa-990e-991b624e015c

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_product_term_ge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_finite_support_set

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
set_option maxHeartbeats 800000
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : letI := piTop;
    Summable (fun p : ℤ × ℕ =>
      (PowerSeries.C (LaurentPolynomial.T p.1) * q ^ p.1.natAbs ^ 2) *
      ((-(q * aI)) ^ p.2 *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1)) := by
  change @Summable R (ℤ × ℕ) _ piTop _ _
  rw [show piTop = PowerSeries.WithPiTopology.instTopologicalSpace (LaurentPolynomial ℤ) from rfl,
    PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  apply summable_of_finite_support
  exact (finite_support_set d).subset (fun ⟨m, ℓ⟩ hmem => by
    simp only [Function.mem_support, Set.mem_setOf_eq] at hmem ⊢
    by_contra h
    push_neg at h
    exact hmem (PowerSeries.coeff_of_lt_order _ (lt_of_lt_of_le (by exact_mod_cast h) (order_product_term_ge m ℓ))))
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
