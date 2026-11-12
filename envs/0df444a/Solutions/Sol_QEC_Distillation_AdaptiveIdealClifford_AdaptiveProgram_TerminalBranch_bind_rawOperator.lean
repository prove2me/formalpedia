-- Prove2me | solution 1 for QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.bind_rawOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:15:49.994148+00:00
-- url     : https://prove2.me/submissions/833d2592-406c-4fe8-afcf-734d77b11015

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
open QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {Wire : Type} [Fintype Wire] {Token : Type}
variable {presentation : CliffordPresentation (H := QubitRegister ι) Wire}
namespace QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram
namespace TerminalBranch
theorem _root_.solution
    (first second : TerminalBranch (ι := ι) (κ := κ) (Token := Token)) :
    (first.bind second).rawOperator =
      (first.weight : Complex) • second.rawOperator := by
  change
    ((↑(first.weight * second.weight) : Complex) • second.output.toOperator) =
      (first.weight : Complex) •
        ((second.weight : Complex) • second.output.toOperator)
  rw [smul_smul]
  congr 1
  norm_cast
end TerminalBranch
end QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram
