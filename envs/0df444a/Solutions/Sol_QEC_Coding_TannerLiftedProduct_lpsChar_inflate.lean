-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChar_inflate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:45:11.041069+00:00
-- url     : https://prove2.me/submissions/96f5c3f7-5c46-45c4-88e4-09708e807dd8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (d m : ℕ) [NeZero d] [NeZero m] (x : ℤ) :
    ZMod.stdAddChar (((m:ℤ)*x:ℤ):ZMod (d*m)) =
      ZMod.stdAddChar (x:ZMod d) := by
  rw [ZMod.stdAddChar_coe,ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hd : (d:ℂ)≠0 := by exact_mod_cast NeZero.ne d
  have hm : (m:ℂ)≠0 := by exact_mod_cast NeZero.ne m
  field_simp
end QEC.Coding.TannerLiftedProduct
