-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_lpsQuaternionShell_eq_prime_add_one_of_theta_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:40:38.861814+00:00
-- url     : https://prove2.me/submissions/4916d603-26cd-4af2-a25b-3a68042ef62f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionFullShell_eq_prime_of_theta_identity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one_of_full_count


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hTheta : integerThetaSeries ^ 4 = jacobiFourSquareSeries) :
    (lpsQuaternionShell p).card = p + 1 :=
  card_lpsQuaternionShell_eq_prime_add_one_of_full_count hp.pos hp4
    (card_lpsQuaternionFullShell_eq_prime_of_theta_identity hp hp4 hTheta)
end QEC.Coding.TannerLiftedProduct
