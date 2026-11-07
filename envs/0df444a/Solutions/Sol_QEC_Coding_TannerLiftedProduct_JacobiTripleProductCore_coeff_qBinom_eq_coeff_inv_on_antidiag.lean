-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_qBinom_eq_coeff_inv_on_antidiag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:28:53.429484+00:00
-- url     : https://prove2.me/submissions/27cf430a-2844-4544-aae3-63b571f90155

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qBinom_coeff_eq_invOfUnit
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qBinom_coeff_eq_invOfUnit_small

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (m k i j : ℕ) (hk : k ≤ m)
    (hij : i + j = m) (_hj : k ^ 2 ≤ j) :
    (qBinom (q ^ 2) (2 * m + 1) k : R).coeff i =
    (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff i := by
  by_cases hki : k ≤ i
  · exact qBinom_coeff_eq_invOfUnit i k (2 * m + 1) hki (by omega)
  · push_neg at hki
    exact qBinom_coeff_eq_invOfUnit_small m k i hk hki (by omega)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
