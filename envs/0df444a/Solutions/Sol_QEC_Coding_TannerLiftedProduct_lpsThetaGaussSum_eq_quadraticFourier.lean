-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaGaussSum_eq_quadraticFourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:52:17.422388+00:00
-- url     : https://prove2.me/submissions/09ab0522-1dc7-4ba3-b292-c55475193fd8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaGaussSum_term

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : ℤ) (N : ℕ) [NeZero N] (z : ℂ) (hz : 0 < z.im) :
    lpsThetaGaussSum a N z =
      ∑' n : ℤ, lpsQuadraticFourier N (a:ZMod N) (n:ZMod N) *
        Complex.exp ((Real.pi:ℂ)*Complex.I*(n:ℂ)^2*z) := by
  have hs (r : Fin N) : Summable (fun n : ℤ =>
      lpsQuadraticPhase a N r * jacobiTheta₂_term n ((r.val:ℂ)/(N:ℂ)) z) :=
    (hasSum_jacobiTheta₂_term ((r.val:ℂ)/(N:ℂ)) hz).summable.mul_left _
  unfold lpsThetaGaussSum jacobiTheta₂
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun r (_ : r ∈ Finset.univ) => hs r)]
  apply tsum_congr
  intro n
  rw [lpsQuadraticFourier,Finset.sum_mul]
  apply Fintype.sum_equiv (ZMod.finEquiv N).toEquiv
  intro r
  exact lpsThetaGaussSum_term a n N r z
end QEC.Coding.TannerLiftedProduct
