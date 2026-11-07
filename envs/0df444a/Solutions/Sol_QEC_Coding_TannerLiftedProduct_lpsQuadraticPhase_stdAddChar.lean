-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticPhase_stdAddChar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:46:03.778479+00:00
-- url     : https://prove2.me/submissions/7e45e420-b2fa-4f78-bdd3-f7526e98a3ec

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFin_cast_finEquiv

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (a : ℤ) (r : Fin N) :
    lpsQuadraticPhase a N r = ZMod.stdAddChar ((a:ZMod N)*(ZMod.finEquiv N r)^2) := by
  rw [← lpsFin_cast_finEquiv]
  have he : (a:ZMod N)*(r.val:ZMod N)^2 = ((a*(r.val:ℤ)^2:ℤ):ZMod N) := by push_cast;rfl
  rw [he,ZMod.stdAddChar_coe]
  unfold lpsQuadraticPhase
  push_cast
  congr 1
  ring
end QEC.Coding.TannerLiftedProduct
