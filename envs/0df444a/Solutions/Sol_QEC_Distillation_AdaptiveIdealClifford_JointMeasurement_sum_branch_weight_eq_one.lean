-- Prove2me | solution 1 for QEC.Distillation.AdaptiveIdealClifford.JointMeasurement.sum_branch_weight_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:51:39.994582+00:00
-- url     : https://prove2.me/submissions/b34f5a17-58e5-4ee3-beb6-bc3db1820373

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_bornWeight_eq_one


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
    (rho : DensityOperator (QubitRegister ι)) :
    ∑ syndrome, (measurement.branch syndrome rho).weight = 1 :=
  measurement.instrument.sum_bornWeight_eq_one
    (jointStabilizerKrausFamily_complete measurement.checks measurement.commute) rho
end QEC.Distillation.AdaptiveIdealClifford.JointMeasurement
