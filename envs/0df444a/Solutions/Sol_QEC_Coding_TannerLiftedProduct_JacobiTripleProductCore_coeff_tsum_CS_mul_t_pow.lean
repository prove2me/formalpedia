-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_tsum_CS_mul_t_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:48:04.169525+00:00
-- url     : https://prove2.me/submissions/6f125d68-b1b1-405c-891e-d532e6e54d61

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_hasSum_CS_mul_t_pow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (c : ℕ → R) (n : ℕ) :
    @PowerSeries.coeff R _ n (letI := piTopS; ∑' k, CS (c k) * t ^ k) = c n := by
  letI := piTopS
  haveI : T2Space S := @PowerSeries.WithPiTopology.instT2Space R piTop
    (@PowerSeries.WithPiTopology.instT2Space (LaurentPolynomial ℤ) ⊥ inferInstance)
  rw [(hasSum_CS_mul_t_pow c).tsum_eq, PowerSeries.coeff_mk]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
