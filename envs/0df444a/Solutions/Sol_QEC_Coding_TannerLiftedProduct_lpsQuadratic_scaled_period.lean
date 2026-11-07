-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadratic_scaled_period
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:46:06.12509+00:00
-- url     : https://prove2.me/submissions/b7e926be-f092-468a-9a79-bcddfbd1e75b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (d m : ℕ) [NeZero d] [NeZero m]
    (a r i : ℤ) :
    ZMod.stdAddChar (((a*(d:ℤ)^2*(r+(m:ℤ)*i)^2):ℤ):ZMod (d*m)) =
      ZMod.stdAddChar (((a*(d:ℤ)^2*r^2):ℤ):ZMod (d*m)) := by
  congr 1
  have hz : (((d:ℤ)*(m:ℤ):ℤ):ZMod (d*m)) = 0 := by
    push_cast
    exact_mod_cast ZMod.natCast_self (d*m)
  calc
    _ = (((a*(d:ℤ)^2*r^2):ℤ):ZMod (d*m)) +
        (((a*(d:ℤ)*(2*r*i+(m:ℤ)*i^2)):ℤ):ZMod (d*m))*
        (((d:ℤ)*(m:ℤ):ℤ):ZMod (d*m)) := by push_cast;ring
    _ = _ := by rw [hz,mul_zero,add_zero]
end QEC.Coding.TannerLiftedProduct
