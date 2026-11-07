-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_lpsQuaternionFullShell_eq_prime_of_theta_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:38:17.195871+00:00
-- url     : https://prove2.me/submissions/4e8f3bf4-8ad7-4486-a414-042fa8670f38

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_integerThetaSeries_pow_four_eq_fullShell_card
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_prime

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hTheta : integerThetaSeries ^ 4 = jacobiFourSquareSeries) :
    (lpsQuaternionFullShell p).card = 8 * (p + 1) := by
  rw [← coeff_integerThetaSeries_pow_four_eq_fullShell_card hp.pos]
  rw [hTheta]
  exact coeff_jacobiFourSquareSeries_prime hp hp4
end QEC.Coding.TannerLiftedProduct
