-- Prove2me | solution 1 for SumProduct.cubeSumLawSuccDensity_lintegral_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:01:58.629028+00:00
-- url     : https://prove2.me/submissions/46965b53-b91d-40a2-bb06-348dc6723b55

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
import Theorems.Thm_SumProduct_cubeSumLaw_succ_eq_withDensity
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
theorem _root_.solution (n : ℕ) :
    (∫⁻ x : ℝ, cubeSumLawSuccDensity n x) ≠ ∞ := by
  have hfin : (volume.withDensity (cubeSumLawSuccDensity n)) Set.univ ≠ ∞ := by
    rw [← cubeSumLaw_succ_eq_withDensity n]
    simp
  rw [withDensity_apply _ MeasurableSet.univ] at hfin
  simpa using hfin
end SumProduct
