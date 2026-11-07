-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_mul_of_trunc_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:20:15.891212+00:00
-- url     : https://prove2.me/submissions/fdc5c71b-574c-4ce3-92d0-db3d24f49327

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_antidiag_sum_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (f g : R) (m : ℕ)
    (hg : ∀ j ≤ m, g.coeff j = if j = 0 then 1 else 0) :
    (f * g).coeff m = f.coeff m := by
  rw [PowerSeries.coeff_mul]
  exact antidiag_sum_eq f g m hg
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
