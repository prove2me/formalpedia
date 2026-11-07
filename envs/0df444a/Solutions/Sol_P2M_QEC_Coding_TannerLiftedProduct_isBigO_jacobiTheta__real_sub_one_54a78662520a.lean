-- Prove2me | solution 1 for P2M_QEC_Coding_TannerLiftedProduct_isBigO_jacobiTheta__real_sub_one_54a78662520a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:46:42.434402+00:00
-- url     : https://prove2.me/submissions/655d14bd-dc56-4d58-b0ed-4571e0bcf55c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_norm_jacobiTheta__real_sub_one_le_053cee2a9de2
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real Filter Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : ℝ) :
    (fun z : ℂ => jacobiTheta₂ (a:ℂ) z-1) =O[comap Complex.im atTop]
      fun z => Real.exp (-Real.pi*z.im) := by
  simp_rw [Asymptotics.IsBigO,Asymptotics.IsBigOWith,Filter.eventually_comap,Filter.eventually_atTop]
  refine ⟨2/(1-Real.exp (-(Real.pi*1))),1,fun y hy z hzy =>
    (norm_jacobiTheta₂_real_sub_one_le a z (hzy.symm ▸ zero_lt_one.trans_le hy)).trans ?_⟩
  rw [Real.norm_eq_abs,Real.abs_exp,hzy,neg_mul]
  gcongr
  simp [Real.pi_pos]
end QEC.Coding.TannerLiftedProduct
