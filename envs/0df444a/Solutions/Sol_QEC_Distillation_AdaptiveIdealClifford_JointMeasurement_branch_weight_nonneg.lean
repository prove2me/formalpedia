-- Prove2me | solution 1 for QEC.Distillation.AdaptiveIdealClifford.JointMeasurement.branch_weight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:51:32.422457+00:00
-- url     : https://prove2.me/submissions/2ac2bc0f-4d3d-4f7e-a14e-016a40b3f22f

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_nonneg


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
open QEC.Distillation.AdaptiveIdealClifford.JointMeasurement
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
namespace QEC.Distillation.AdaptiveIdealClifford.JointMeasurement
theorem _root_.solution (measurement : JointMeasurement ι κ)
    (syndrome : JointSyndrome κ) (rho : DensityOperator (QubitRegister ι)) :
    0 ≤ (measurement.branch syndrome rho).weight :=
  measurement.instrument.bornWeight_nonneg syndrome rho
end QEC.Distillation.AdaptiveIdealClifford.JointMeasurement
