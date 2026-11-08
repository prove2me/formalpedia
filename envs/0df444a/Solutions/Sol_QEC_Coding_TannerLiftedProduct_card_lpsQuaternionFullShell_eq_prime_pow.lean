-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_lpsQuaternionFullShell_eq_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:09:38.974498+00:00
-- url     : https://prove2.me/submissions/3276234d-4b5e-41fc-b0d4-07b40bcac3c0

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimePowerCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_prime_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_integerThetaSeries_pow_four_eq_fullShell_card
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_integerThetaSeries_pow_four_eq_jacobiFourSquareSeries


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hp : p.Prime) (hp4 : p % 4 = 1) (k : ℕ) :
    (lpsQuaternionFullShell (p ^ k)).card =
      8 * ∑ i ∈ Finset.range (k + 1), p ^ i := by
  rw [← coeff_integerThetaSeries_pow_four_eq_fullShell_card
      (pow_pos hp.pos k),
    integerThetaSeries_pow_four_eq_jacobiFourSquareSeries]
  exact coeff_jacobiFourSquareSeries_prime_pow hp hp4 k
end QEC.Coding.TannerLiftedProduct
