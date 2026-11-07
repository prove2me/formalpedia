-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.T_finite_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:53:29.160393+00:00
-- url     : https://prove2.me/submissions/75222162-4e33-4bc3-b7a4-96e5f8de83b6

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_V_coeff_neg_eq_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_finite_exponent_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_monomial_mul_V

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j : ℕ) (b : ℤ) :
    (Function.support (fun ℓ : ℕ ↦ ((-A_hahn j) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ).coeff b)).Finite :=
  (finite_exponent_le j b).subset fun ℓ hℓ => by
    simp only [Function.mem_support, ne_eq, Set.mem_setOf_eq] at hℓ ⊢; by_contra h; push_neg at h
    exact hℓ (by rw [coeff_monomial_mul_V, V_coeff_neg_eq_zero ℓ _ (by omega), mul_zero])
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
