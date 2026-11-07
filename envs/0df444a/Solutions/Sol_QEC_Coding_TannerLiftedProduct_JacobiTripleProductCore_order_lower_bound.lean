-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:10:23.123534+00:00
-- url     : https://prove2.me/submissions/d5a8ceab-2f21-461b-a1c3-fae8dbecdbed

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_q_pow_ge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (i : ℕ) :
    (-x * q).order + 2 * i ≤ ((-x * q) * (q ^ 2) ^ i).order :=
  calc (-x * q).order + 2 * (i : ℕ∞)
      _ ≤ (-x * q).order + (q ^ (2 * i) : R).order := by
          gcongr
          exact order_q_pow_ge (2 * i)
      _ ≤ (-x * q).order + ((q ^ 2) ^ i : R).order := by rw [pow_mul]
      _ ≤ _ := PowerSeries.order_mul_ge _ _
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
