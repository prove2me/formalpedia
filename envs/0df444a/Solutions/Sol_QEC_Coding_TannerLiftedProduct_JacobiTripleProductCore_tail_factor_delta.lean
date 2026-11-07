-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tail_factor_delta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:22:43.116331+00:00
-- url     : https://prove2.me/submissions/4d4d2e9d-ae37-4524-800c-fd388dfb623d

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_factor_coeff_eq_ite

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (m n : ℕ) (hmn : m < n) (i : ℕ)
    (j : ℕ) (hj : j ≤ m) :
    ((1 - ((-x * q) * (q ^ 2) ^ n) * (q ^ 2) ^ i : R)).coeff j =
    if j = 0 then 1 else 0 := by
  rw [show ((-x * q) * (q ^ 2) ^ n) * (q ^ 2) ^ i = (-x * q) * (q ^ 2) ^ (n + i) by ring]
  exact factor_coeff_eq_ite x j (n + i) (by omega)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
