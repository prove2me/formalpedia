-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCRT_linear_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:52:28.656083+00:00
-- url     : https://prove2.me/submissions/e739744b-4459-4fad-b055-895d4fc5ff2b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFin_cast_finEquiv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n) :
    Function.Bijective (fun r : Fin m × Fin n =>
      ((n*r.1.val+m*r.2.val:ℕ):ZMod (m*n))) := by
  classical
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro r s he
    have hm := congrArg (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m)) he
    have hn := congrArg (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n)) he
    simp only [map_add,map_mul,map_natCast,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,
      zero_mul,add_zero,zero_add] at hm hn
    have h1 := ((ZMod.isUnit_iff_coprime n m).mpr h.symm).mul_left_cancel hm
    have h2 := ((ZMod.isUnit_iff_coprime m n).mpr h).mul_left_cancel hn
    apply Prod.ext
    · apply (ZMod.finEquiv m).injective
      simpa only [lpsFin_cast_finEquiv] using h1
    · apply (ZMod.finEquiv n).injective
      simpa only [lpsFin_cast_finEquiv] using h2
  · simp [ZMod.card]
end QEC.Coding.TannerLiftedProduct
