-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChar_inflate_modulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:46:27.200533+00:00
-- url     : https://prove2.me/submissions/5a5e88a5-8670-4cce-b427-bcb9a48382fc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_inflate

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N d m : ℕ) [NeZero N] [NeZero d] [NeZero m]
    (hN : N=d*m) (x : ℤ) :
    ZMod.stdAddChar (((m:ℤ)*x:ℤ):ZMod N) = ZMod.stdAddChar (x:ZMod d) := by
  subst N
  exact lpsChar_inflate d m x
end QEC.Coding.TannerLiftedProduct
