-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChar_mask_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:46:28.4269+00:00
-- url     : https://prove2.me/submissions/f046863e-5723-4c96-875b-cbf058cc92a7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_inflate
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFin_cast_finEquiv


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (d m : ℕ) [NeZero d] [NeZero m] (r : ℤ) :
    (∑ j : Fin d, ZMod.stdAddChar (((m:ℤ)*j.val*r:ℤ):ZMod (d*m))) =
      if (r:ZMod d)=0 then (d:ℂ) else 0 := by
  classical
  have h := AddChar.sum_mulShift (r:ZMod d) (ZMod.isPrimitive_stdAddChar d)
  rw [ZMod.card] at h
  push_cast at h
  rw [← h]
  apply Fintype.sum_equiv (ZMod.finEquiv d).toEquiv
  intro j
  rw [show ((m:ℤ)*j.val*r:ℤ)=(m:ℤ)*(j.val*r) by ring,lpsChar_inflate]
  change ZMod.stdAddChar (((j.val:ℤ)*r:ℤ):ZMod d) =
    ZMod.stdAddChar (ZMod.finEquiv d j*(r:ZMod d))
  rw [← lpsFin_cast_finEquiv]
  push_cast
  rfl
end QEC.Coding.TannerLiftedProduct
