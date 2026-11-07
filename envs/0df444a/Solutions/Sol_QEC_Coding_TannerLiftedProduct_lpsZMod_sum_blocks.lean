-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsZMod_sum_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:46:01.47721+00:00
-- url     : https://prove2.me/submissions/3c7fb4b3-3823-4378-8b8c-be7a6bc580d2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFin_cast_finEquiv


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (d m : ℕ) [NeZero d] [NeZero m] (f : ZMod (d*m) → ℂ) :
    (∑ r : ZMod (d*m), f r) =
      ∑ i : Fin d, ∑ j : Fin m, f ((j.val+m*i.val:ℕ):ZMod (d*m)) := by
  classical
  rw [← Fintype.sum_prod_type']
  symm
  apply Fintype.sum_equiv (finProdFinEquiv.trans (ZMod.finEquiv (d*m)).toEquiv)
  intro r
  change f ((r.2.val+m*r.1.val:ℕ):ZMod (d*m)) =
    f (ZMod.finEquiv (d*m) (finProdFinEquiv r))
  exact congrArg f (lpsFin_cast_finEquiv (d*m) (finProdFinEquiv r))
end QEC.Coding.TannerLiftedProduct
