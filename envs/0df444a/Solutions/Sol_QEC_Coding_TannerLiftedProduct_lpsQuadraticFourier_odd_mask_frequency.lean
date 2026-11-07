-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticFourier_odd_mask_frequency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:52:40.407112+00:00
-- url     : https://prove2.me/submissions/ed64abb5-7c08-431c-ae8d-f890d73b6cda

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_completeSquare
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_zero_eq_Gauss
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N d k : ℕ) [NeZero N]
    (hN : N=d^2*k) (a : ℤ) (ha : IsUnit (a:ZMod N))
    (h2 : IsUnit (2:ZMod N)) (j : ℤ) :
    lpsQuadraticFourier N (a:ZMod N) (((d:ℤ)*(k:ℤ)*j:ℤ):ZMod N) =
      lpsUnaryQuadraticGauss a N := by
  let u : ZMod N := ↑(ha.unit⁻¹)
  let v : ZMod N := ↑(h2.unit⁻¹)
  have had : (a:ZMod N)*u=1 := by
    have h : (ha.unit:ZMod N)*↑(ha.unit⁻¹)=1 := by simp
    simpa only [ha.unit_spec,u] using h
  have hv : (2:ZMod N)*v=1 := by
    have h : (h2.unit:ZMod N)*↑(h2.unit⁻¹)=1 := by simp
    simpa only [h2.unit_spec,v] using h
  let t : ZMod N := (d:ZMod N)*(k:ZMod N)*u*v*(j:ZMod N)
  have hn : (((d:ℤ)*(k:ℤ)*j:ℤ):ZMod N)=2*(a:ZMod N)*t := by
    dsimp [t]
    push_cast
    calc
      _ = ((2:ZMod N)*v)*((a:ZMod N)*u)*(d:ZMod N)*(k:ZMod N)*(j:ZMod N) := by
        rw [hv,had];ring
      _ = _ := by ring
  have hphase : -(a:ZMod N)*t^2=0 := by
    dsimp [t]
    calc
      _ = (-(a:ZMod N)*(k:ZMod N)*u^2*v^2*(j:ZMod N)^2)*(N:ZMod N) := by
        have hncast := congrArg (fun x : ℕ => (x:ZMod N)) hN
        push_cast at hncast
        rw [hncast]
        ring
      _ = 0 := by rw [ZMod.natCast_self,mul_zero]
  rw [hn,lpsQuadraticFourier_completeSquare,hphase,AddChar.map_zero_eq_one,one_mul,
    lpsQuadraticFourier_zero_eq_Gauss]
end QEC.Coding.TannerLiftedProduct
