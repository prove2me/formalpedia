-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsZMod_sum_residue_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:46:07.247211+00:00
-- url     : https://prove2.me/submissions/48e08b4e-79a3-4b14-ac19-f04c6840c7fc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFin_cast_finEquiv


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (d m : ℕ) [NeZero d] [NeZero m]
    (f : ZMod (d*m) → ℂ) :
    (∑ r : ZMod (d*m), f r) =
      ∑ i : Fin m, ∑ j : Fin d, f ((j.val+d*i.val:ℕ):ZMod (d*m)) := by
  classical
  rw [← Fintype.sum_prod_type']
  symm
  apply Fintype.sum_equiv
    (finProdFinEquiv.trans ((finCongr (Nat.mul_comm m d)).trans
      (ZMod.finEquiv (d*m)).toEquiv))
  intro r
  change f ((r.2.val+d*r.1.val:ℕ):ZMod (d*m)) =
    f (ZMod.finEquiv (d*m) ((finCongr (Nat.mul_comm m d)) (finProdFinEquiv r)))
  rw [← lpsFin_cast_finEquiv]
  rfl
end QEC.Coding.TannerLiftedProduct
