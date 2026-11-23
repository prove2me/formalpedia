-- Prove2me | solution 1 for SumProduct.cubeSumLaw_Icc_toReal_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:55:56.793138+00:00
-- url     : https://prove2.me/submissions/8db2640e-24a1-4e2b-90e4-9db2f5897a0f

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
import Theorems.Thm_SumProduct_cubeSection_one_eq_unitCube_inter_sum

set_option autoImplicit true
open MeasureTheory
open scoped ENNReal MeasureTheory FourierTransform
open SumProduct
noncomputable section
namespace SumProduct
theorem _root_.solution (n : ℕ) :
    (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal =
      (volume (cubeSection (Fin n) 1)).toReal / (2 : ℝ) ^ n := by
  change (cubeSumLaw n).real (Set.Icc (-1 : ℝ) 1) =
    volume.real (cubeSection (Fin n) 1) / (2 : ℝ) ^ n
  rw [cubeSumLaw, map_measureReal_apply (measurable_coordSum n) measurableSet_Icc]
  rw [uniformCubeMeasure, measureReal_ennreal_smul_apply]
  rw [measureReal_restrict_apply ((measurable_coordSum n) measurableSet_Icc)]
  rw [Set.inter_comm, ← cubeSection_one_eq_unitCube_inter_sum n, volume_unitCube]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (pow_nonneg zero_le_two n)]
  rw [div_eq_mul_inv, mul_comm]
end SumProduct
