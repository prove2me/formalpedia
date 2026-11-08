-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_lpsQuaternionShell_eq_prime_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:13:47.177196+00:00
-- url     : https://prove2.me/submissions/6c11688d-a5cc-400c-80c4-645703c0e153

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one_of_theta_identity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_integerThetaSeries_pow_four_eq_jacobiFourSquareSeries


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    (lpsQuaternionShell p).card = p + 1 :=
  card_lpsQuaternionShell_eq_prime_add_one_of_theta_identity hp hp4
    integerThetaSeries_pow_four_eq_jacobiFourSquareSeries
end QEC.Coding.TannerLiftedProduct
