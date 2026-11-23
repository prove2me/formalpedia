-- Prove2me | solution 1 for SumProduct.cubeSection_one_eq_unitCube_inter_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:53:24.546179+00:00
-- url     : https://prove2.me/submissions/140818d4-98dc-4859-9ed3-f1ac047b3e4d

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
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
    cubeSection (Fin n) 1 =
      unitCube n ∩ (coordSum n) ⁻¹' Set.Icc (-1 : ℝ) 1 := by
  ext x
  simp [cubeSection, unitCube, coordSum, abs_le, Pi.le_def, forall_and]
end SumProduct
