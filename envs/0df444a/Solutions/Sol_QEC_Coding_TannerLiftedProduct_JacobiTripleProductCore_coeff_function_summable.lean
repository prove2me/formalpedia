-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_function_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:53:47.222357+00:00
-- url     : https://prove2.me/submissions/adf4676c-b02f-45e7-9887-ffef316f91b7

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_support_finset_bound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_summand_vanishes

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (d : ℕ) :
    Summable (fun (p : ℕ × ℕ) =>
      (PowerSeries.coeff d)
        (PowerSeries.C (LaurentPolynomial.T (p.1 : ℤ)) *
         ((-1 : R) ^ p.2 * q ^ ((p.1 + p.2) ^ 2 + p.2)) *
         PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1)) := by
  obtain ⟨S, hS⟩ := support_finset_bound d
  exact summable_of_ne_finset_zero (s := S) fun ⟨k, ℓ⟩ hkl =>
    coeff_summand_vanishes k ℓ d (by contrapose! hkl; exact hS k ℓ hkl)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
