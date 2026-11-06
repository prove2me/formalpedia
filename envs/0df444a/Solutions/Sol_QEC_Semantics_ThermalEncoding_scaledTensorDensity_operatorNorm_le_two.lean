-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.scaledTensorDensity_operatorNorm_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:03:47.058535+00:00
-- url     : https://prove2.me/submissions/d2f616ee-4054-4a5f-91ef-be441917e536

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Semantics_ThermalEncoding_tensorDensityLeft_operatorNorm_le_one

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.ThermalEncoding
open Classical
open scoped BigOperators ComplexOrder TensorProduct
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics.ThermalEncoding
theorem _root_.solution {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) :
    ‖LinearMap.toContinuousLinearMap
      (TensorProduct.map ((2 : Complex) • rho.toOperator)
        (1 : Operator K))‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖TensorProduct.map ((2 : Complex) • rho.toOperator)
      (1 : Operator K) x‖ ≤ 2 * ‖x‖
  rw [TensorProduct.map_smul_left]
  change ‖(2 : Complex) •
      TensorProduct.map rho.toOperator (1 : Operator K) x‖ ≤ 2 * ‖x‖
  rw [norm_smul]
  norm_num
  calc
    ‖TensorProduct.map rho.toOperator (1 : Operator K) x‖ ≤
        ‖LinearMap.toContinuousLinearMap
          (TensorProduct.map rho.toOperator (1 : Operator K))‖ * ‖x‖ :=
      (LinearMap.toContinuousLinearMap
        (TensorProduct.map rho.toOperator (1 : Operator K))).le_opNorm x
    _ ≤ 1 * ‖x‖ := by
      gcongr
      exact tensorDensityLeft_operatorNorm_le_one rho
    _ = ‖x‖ := one_mul _
end QEC.Semantics.ThermalEncoding
