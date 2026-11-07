-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.eval_B
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:58:16.212187+00:00
-- url     : https://prove2.me/submissions/5030c48d-1cb2-438b-a7c6-5950a7200d98

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_exponent_simp
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_euler_product
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_eval_x_tsum_coeff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (hx : x.constantCoeff = 0) : letI := piTop;
    eval_x_fun x B_S = qPochhammerInf (-x) (q ^ 2) := by
  rw [show B_S = (letI := piTopS; ∑' k, CS (bCoeff k) * t ^ k) from rfl,
      eval_x_tsum_coeff x hx bCoeff]
  obtain ⟨y, hxy⟩ := PowerSeries.X_dvd_iff.mpr hx
  show letI := piTop; (∑' k, bCoeff k * x ^ k) = qPochhammerInf (-x) (q ^ 2)
  conv_rhs => rw [show (-x : R) = -y * q by rw [hxy]; ring]
  rw [euler_product y]
  letI := piTop
  refine tsum_congr fun k => ?_
  simp only [bCoeff]
  rw [hxy]
  have h := exponent_simp y k
  set_option maxRecDepth 1024 in
  rw [show (-(-y * q)) ^ k = (y * q) ^ k by simp [neg_neg]] at h
  rw [show (PowerSeries.X * y) ^ k = (y * q) ^ k by show (q * y) ^ k = _; rw [mul_comm],
      show (q ^ 2) ^ k.choose 2 * PowerSeries.invOfUnit (P k) 1 * (y * q) ^ k =
        (y * q) ^ k * (q ^ 2) ^ k.choose 2 * PowerSeries.invOfUnit (P k) 1 by ring, h]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
