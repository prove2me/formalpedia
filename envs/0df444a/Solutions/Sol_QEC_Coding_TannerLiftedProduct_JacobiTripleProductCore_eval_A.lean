-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.eval_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:51:55.496944+00:00
-- url     : https://prove2.me/submissions/be1c3026-1d8b-4a6f-b26a-df9ef8382b42

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_eval_x_tsum_coeff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (hx : x.constantCoeff = 0) : letI := piTop;
    eval_x_fun x A_S =
    ∑' ℓ, (-x) ^ ℓ * PowerSeries.invOfUnit (P ℓ) 1 := by
  show letI := piTop; eval_x_fun x A_S = ∑' ℓ, (-x) ^ ℓ * PowerSeries.invOfUnit (P ℓ) 1
  rw [show A_S = (letI := piTopS; ∑' ℓ, CS (aCoeff ℓ) * t ^ ℓ) from rfl,
      eval_x_tsum_coeff x hx aCoeff]
  letI := piTop
  refine tsum_congr fun ℓ => ?_
  simp only [aCoeff]
  set_option maxRecDepth 1024 in
  rw [show (-x) ^ ℓ = (-1 : R) ^ ℓ * x ^ ℓ from neg_one_mul x ▸ mul_pow (-1) x ℓ]
  ring
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
