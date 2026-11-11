-- Prove2me | solution 1 for QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_coin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:55:27.644405+00:00
-- url     : https://prove2.me/submissions/22df00af-a925-498d-a24f-6fba37b6d832

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
theorem _root_.solution
    (next : Bool → AdaptiveProgram κ Token presentation)
    (rho : DensityOperator (QubitRegister ι)) :
    (coin next).eval rho =
      ((next false).eval rho).map (TerminalBranch.prependCoin false) +
        ((next true).eval rho).map (TerminalBranch.prependCoin true) :=
  rfl
end QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram
