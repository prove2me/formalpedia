-- Prove2me | solution 1 for QEC.Distillation.AdaptiveIdealClifford.ZeroPreparationAdapter.run_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:53:50.333418+00:00
-- url     : https://prove2.me/submissions/cc117862-c853-4c36-b625-bdfdef4ec5b4

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.AdaptiveIdealClifford
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct
universe u v w
variable {H K R E : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]
variable [NormedAddCommGroup R] [InnerProductSpace Complex R]
  [FiniteQuantumSystem R]
variable [NormedAddCommGroup E] [InnerProductSpace Complex E]
  [FiniteQuantumSystem E]
open QEC.Distillation.AdaptiveIdealClifford.ZeroPreparationAdapter
variable {H K : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Distillation.AdaptiveIdealClifford.ZeroPreparationAdapter
theorem _root_.solution (adapter : ZeroPreparationAdapter (H := H) (K := K))
    (rho : DensityOperator H) :
    (adapter.run rho).toOperator =
      adapter.consumer (DensityOperator.tensorDensity rho zeroQubitDensity).toOperator :=
  rfl
end QEC.Distillation.AdaptiveIdealClifford.ZeroPreparationAdapter
