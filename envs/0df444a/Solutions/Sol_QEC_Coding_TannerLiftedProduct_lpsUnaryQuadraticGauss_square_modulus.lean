-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_square_modulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:55:58.227203+00:00
-- url     : https://prove2.me/submissions/4e1cac91-c81d-436a-abee-f4af45749fd2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_square_scale
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_inflate

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (d k : ℕ) (hd : 0 < d) (hk : 0 < k)
    (a b u : ℤ) (hdet : a*u-b*((4*d^2*k:ℕ):ℤ)=1) :
    lpsUnaryQuadraticGauss a (4*d^2*k) =
      (d:ℂ)*lpsUnaryQuadraticGauss a (4*k) := by
  let : NeZero d := ⟨ne_of_gt hd⟩
  let : NeZero k := ⟨ne_of_gt hk⟩
  have hi := lpsUnaryQuadraticGauss_inflate (d^2) (4*k) a
  have hm : d^2*(4*k)=4*d^2*k := by ring
  rw [hm] at hi
  norm_num only [Nat.cast_pow] at hi
  have hs := lpsUnaryQuadraticGauss_square_scale (4*d^2*k) d k rfl hd hk a b u hdet
  rw [hs] at hi
  have hdC : (d:ℂ)≠0 := by exact_mod_cast ne_of_gt hd
  apply mul_left_cancel₀ hdC
  calc
    _ = (d:ℂ)^2*lpsUnaryQuadraticGauss a (4*k) := hi
    _ = _ := by ring
end QEC.Coding.TannerLiftedProduct
