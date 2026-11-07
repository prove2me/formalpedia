-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.eval_x_tsum_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:49:31.204222+00:00
-- url     : https://prove2.me/submissions/7e358cb5-09e6-4466-b0a2-39ad086b7e33

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_tsum_CS_mul_t_pow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (_hx : x.constantCoeff = 0) (c : ℕ → R) :
    eval_x_fun x (letI := piTopS; ∑' n, CS (c n) * t ^ n) =
    (letI := piTop; ∑' n, c n * x ^ n) := by
  show letI := piTop; ∑' d, (letI := piTopS; ∑' n, CS (c n) * t ^ n).coeff d * x ^ d =
    ∑' n, c n * x ^ n
  letI := piTop
  congr 1
  funext d
  rw [coeff_tsum_CS_mul_t_pow c d]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
