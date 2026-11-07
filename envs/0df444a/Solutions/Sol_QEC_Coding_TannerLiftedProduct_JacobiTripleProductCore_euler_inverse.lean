-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.euler_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:59:46.390209+00:00
-- url     : https://prove2.me/submissions/bcbc590f-3761-49fa-bb9f-6d3006973a58

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_AB_eq_one_in_S
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_eval_x_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_eval_x_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_eval_A
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_eval_B

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (hx : x.constantCoeff = 0) : letI := piTop;
    (∑' ℓ : ℕ, (-x) ^ ℓ *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) *
    qPochhammerInf (-x) (q ^ 2) = 1 := by
  have h := eval_x_mul x hx A_S B_S
  rw [AB_eq_one_in_S, eval_x_one x hx] at h
  rw [← eval_A x hx, ← eval_B x hx]
  exact h.symm
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
