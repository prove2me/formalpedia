-- Prove2me | solution 1 for SumProduct.cubeSumLaw_measure_Icc_toReal_eq_integral_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:06:35.169385+00:00
-- url     : https://prove2.me/submissions/9c1f8605-e3d3-4bda-beea-07d0dfd63aed

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
import Theorems.Thm_SumProduct_cubeSumLaw_succ_eq_withDensity
import Theorems.Thm_SumProduct_measurable_cubeSumLawSuccDensity
import Theorems.Thm_SumProduct_cubeSumLawSuccDensity_ae_lt_top
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
theorem _root_.solution (m : ℕ) (a b : ℝ) :
    (cubeSumLaw (m + 1) (Set.Icc a b)).toReal =
      ∫ x in Set.Icc a b, (cubeSumLawSuccDensity m x).toReal := by
  let s := Set.Icc a b
  have hs : MeasurableSet s := measurableSet_Icc
  have htop : ∀ᵐ x ∂volume.restrict s, cubeSumLawSuccDensity m x < ∞ := by
    exact ae_restrict_of_ae (cubeSumLawSuccDensity_ae_lt_top m)
  have h := setIntegral_withDensity_eq_setIntegral_toReal_smul
      (μ := volume) (f := cubeSumLawSuccDensity m) (s := s)
      (measurable_cubeSumLawSuccDensity m) htop (fun _ : ℝ => (1 : ℝ)) hs
  have h' : ((volume.withDensity (cubeSumLawSuccDensity m)) s).toReal =
      ∫ x in s, (cubeSumLawSuccDensity m x).toReal := by
    simpa [measureReal_def] using h
  rw [cubeSumLaw_succ_eq_withDensity m]
  simpa [s] using h'
end SumProduct
