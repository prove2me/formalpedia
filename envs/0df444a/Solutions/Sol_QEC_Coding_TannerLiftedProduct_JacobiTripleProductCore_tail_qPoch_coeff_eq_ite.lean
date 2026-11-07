-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tail_qPoch_coeff_eq_ite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:46:01.917813+00:00
-- url     : https://prove2.me/submissions/455d1a62-4f54-4ca9-be2a-2d0ee1218b24

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_prod_coeff_delta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_factor_coeff_eq_delta

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (m k n : ℕ) (hn : m + k + 1 ≤ n) (j : ℕ) (hj : j ≤ m) :
    (qPoch (q ^ 2 * (q ^ 2) ^ (n - k)) (q ^ 2) k : R).coeff j =
    if j = 0 then 1 else 0 := by
  apply prod_coeff_delta m (fun i => 1 - q ^ 2 * (q ^ 2) ^ (n - k) * (q ^ 2) ^ i) k _ j hj
  intro i hi j' hj'
  show ((1 - q ^ 2 * (q ^ 2) ^ (n - k) * (q ^ 2) ^ i : R)).coeff j' = _
  rw [show q ^ 2 * (q ^ 2) ^ (n - k) * (q ^ 2) ^ i = (q : R) ^ (2 * (n - k + 1 + i)) by
    rw [← pow_mul q 2, ← pow_add, ← pow_mul q 2, ← pow_add]
    congr 1
    omega]
  exact factor_coeff_eq_delta m (n - k + 1 + i) (by omega) j' hj'
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
