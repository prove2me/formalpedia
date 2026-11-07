-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_odd_square_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:55:32.913203+00:00
-- url     : https://prove2.me/submissions/9f55a593-3ccd-42aa-b14c-445d6c99dd57

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_odd_mask_frequency
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticGauss_mask_sum_modulus
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N d k : ℕ) [NeZero N]
    (hN : N=d^2*k) (hd : 0 < d) (hk : 0 < k) (a : ℤ)
    (ha : IsUnit (a:ZMod N)) (h2 : IsUnit (2:ZMod N)) :
    lpsUnaryQuadraticGauss (a*(d:ℤ)^2) N=(d:ℂ)*lpsUnaryQuadraticGauss a N := by
  let : NeZero d := ⟨ne_of_gt hd⟩
  let : NeZero k := ⟨ne_of_gt hk⟩
  have hNm : N=d*(d*k) := by rw [hN];ring
  have hmask := lpsQuadraticGauss_mask_sum_modulus N d (d*k) hNm a
  have hf (j : Fin d) :
      lpsQuadraticFourier N (a:ZMod N) ((((d*k:ℕ):ℤ)*j.val:ℤ):ZMod N) =
        lpsUnaryQuadraticGauss a N := by
    have h := lpsQuadraticFourier_odd_mask_frequency N d k hN a ha h2 j.val
    simpa only [Nat.cast_mul] using h
  simp_rw [hf] at hmask
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hmask.symm
end QEC.Coding.TannerLiftedProduct
