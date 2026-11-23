-- Prove2me | solution 1 for SumProduct.charFun_cubeSumLaw_eq_sinc_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:54:52.399882+00:00
-- url     : https://prove2.me/submissions/70d1ff27-ac41-480e-b06d-358c1d6ec8c8

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
import Theorems.Thm_SumProduct_cubeSumLaw_eq_map_pi_sum
import Theorems.Thm_SumProduct_charFun_uniformIntervalMeasure
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
theorem _root_.solution (n : ℕ) (t : ℝ) :
    charFun (cubeSumLaw n) t = (Real.sinc t : ℂ) ^ n := by
  rw [cubeSumLaw_eq_map_pi_sum]
  change charFun ((Measure.pi fun _ : Fin n => uniformIntervalMeasure).map
    (fun p : Fin n → ℝ => ∑ i, p i)) t = (Real.sinc t : ℂ) ^ n
  rw [ProbabilityTheory.charFun_map_sum_pi_eq_prod]
  simp [charFun_uniformIntervalMeasure, Finset.prod_const]
end SumProduct
