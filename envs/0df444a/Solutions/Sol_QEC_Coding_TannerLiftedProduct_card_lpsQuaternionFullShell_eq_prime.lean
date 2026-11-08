-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_lpsQuaternionFullShell_eq_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:40:40.193708+00:00
-- url     : https://prove2.me/submissions/ecedf00f-bc02-43c6-9136-f4a7704a05cb

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionFullShell_eq_prime_of_theta_identity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_integerThetaSeries_pow_four_eq_jacobiFourSquareSeries


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    (lpsQuaternionFullShell p).card = 8 * (p + 1) :=
  card_lpsQuaternionFullShell_eq_prime_of_theta_identity hp hp4
    integerThetaSeries_pow_four_eq_jacobiFourSquareSeries
end QEC.Coding.TannerLiftedProduct
