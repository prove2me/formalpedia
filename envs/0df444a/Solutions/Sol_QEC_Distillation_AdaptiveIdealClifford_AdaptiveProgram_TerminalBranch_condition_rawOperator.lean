-- Prove2me | solution 1 for QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.condition_rawOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:16:18.445173+00:00
-- url     : https://prove2.me/submissions/b530518f-99f4-40ca-aace-7e54e4bcd5ea

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
    (eventMass : ℝ) (hpositive : 0 < eventMass)
    (branch : TerminalBranch (ι := ι) (κ := κ) (Token := Token)) :
    (branch.condition eventMass hpositive).rawOperator =
      (eventMass : Complex)⁻¹ • branch.rawOperator := by
  change
    ((↑(eventMass⁻¹ * branch.weight) : Complex) • branch.output.toOperator) =
      (eventMass : Complex)⁻¹ •
        ((branch.weight : Complex) • branch.output.toOperator)
  rw [smul_smul]
  congr 1
  norm_cast
end TerminalBranch
end QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram
