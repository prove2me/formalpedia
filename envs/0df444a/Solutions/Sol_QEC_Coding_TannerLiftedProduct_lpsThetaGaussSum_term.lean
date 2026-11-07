-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaGaussSum_term
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:46:04.944997+00:00
-- url     : https://prove2.me/submissions/00c2cf83-3ee8-4c16-81a8-734e740b988d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFin_cast_finEquiv

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a n : ℤ) (N : ℕ) [NeZero N] (r : Fin N) (z : ℂ) :
    lpsQuadraticPhase a N r * jacobiTheta₂_term n ((r.val:ℂ)/(N:ℂ)) z =
      ZMod.stdAddChar ((a:ZMod N)*(ZMod.finEquiv N r)^2+(n:ZMod N)*(ZMod.finEquiv N r)) *
        Complex.exp ((Real.pi:ℂ)*Complex.I*(n:ℂ)^2*z) := by
  rw [← lpsFin_cast_finEquiv]
  have he : (a:ZMod N)*(r.val:ZMod N)^2+(n:ZMod N)*(r.val:ZMod N) =
      ((a*(r.val:ℤ)^2+n*(r.val:ℤ):ℤ):ZMod N) := by push_cast;rfl
  rw [he,ZMod.stdAddChar_coe]
  unfold lpsQuadraticPhase jacobiTheta₂_term
  rw [← Complex.exp_add,← Complex.exp_add]
  push_cast
  congr 1
  ring
end QEC.Coding.TannerLiftedProduct
