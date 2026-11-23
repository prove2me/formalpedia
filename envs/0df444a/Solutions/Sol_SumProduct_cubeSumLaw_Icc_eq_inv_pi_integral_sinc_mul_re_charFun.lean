-- Prove2me | solution 1 for SumProduct.cubeSumLaw_Icc_eq_inv_pi_integral_sinc_mul_re_charFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:16:38.914825+00:00
-- url     : https://prove2.me/submissions/cd59da4e-9136-4489-98ea-7439afc37847

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
import Theorems.Thm_SumProduct_charFun_cubeSumLaw_eq_sinc_pow
import Theorems.Thm_SumProduct_cubeSumLaw_Icc_eq_inv_pi_integral_re_charFun_succ
import Theorems.Thm_SumProduct_mem_boxMult
import Theorems.Thm_SumProduct_mem_cubeSection
attribute [local simp] SumProduct.mem_boxMult
attribute [local simp] SumProduct.mem_cubeSection



set_option autoImplicit true
open MeasureTheory
open scoped ENNReal MeasureTheory FourierTransform
open SumProduct
noncomputable section
namespace SumProduct
theorem _root_.solution (n : ℕ) (_hn : 1 ≤ n) :
    (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal =
      (Real.pi)⁻¹ * ∫ t : ℝ, Real.sinc t * (charFun (cubeSumLaw n) t).re := by
  rw [cubeSumLaw_Icc_eq_inv_pi_integral_re_charFun_succ n _hn]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [charFun_cubeSumLaw_eq_sinc_pow (n + 1) t, charFun_cubeSumLaw_eq_sinc_pow n t]
  have hre : ∀ m : ℕ, ((Real.sinc t : ℂ) ^ m).re = (Real.sinc t) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, pow_succ, Complex.mul_re, ih]
        simp
  rw [hre (n + 1), hre n]
  rw [pow_succ]
  ring
end SumProduct
