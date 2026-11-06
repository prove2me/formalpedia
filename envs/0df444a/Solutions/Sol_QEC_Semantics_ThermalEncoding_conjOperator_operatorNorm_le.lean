-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.conjOperator_operatorNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:57:36.424557+00:00
-- url     : https://prove2.me/submissions/e558890c-55ee-4d83-8133-1b9e0dee6992

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding

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
    (U : UnitaryTransport H K) (A : Operator H) :
    ‖LinearMap.toContinuousLinearMap (U.conjOperator A)‖ ≤
      ‖LinearMap.toContinuousLinearMap A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖U.conjOperator A x‖ ≤
    ‖LinearMap.toContinuousLinearMap A‖ * ‖x‖
  rw [UnitaryTransport.conjOperator_apply]
  calc
    ‖U (A (U.toLinearEquiv.symm x))‖ =
        ‖A (U.toLinearEquiv.symm x)‖ := by
          exact U.toLinearIsometryEquiv.norm_map _
    _ ≤ ‖LinearMap.toContinuousLinearMap A‖ *
        ‖U.toLinearEquiv.symm x‖ :=
      (LinearMap.toContinuousLinearMap A).le_opNorm _
    _ = ‖LinearMap.toContinuousLinearMap A‖ * ‖x‖ := by
      congr 1
      exact U.symm.toLinearIsometryEquiv.norm_map x
end QEC.Semantics.ThermalEncoding
