-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsFin_cast_finEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:44:42.644721+00:00
-- url     : https://prove2.me/submissions/d0fdc592-caa3-4ab0-aed5-067dd7974f41

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (r : Fin N) :
    (r.val:ZMod N) = ZMod.finEquiv N r := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N => exact ZMod.natCast_zmod_val (n:=N+1) r
end QEC.Coding.TannerLiftedProduct
