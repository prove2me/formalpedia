-- Prove2me | solution 1 for QEC.Distillation.AdaptiveIdealClifford.DeterministicStep.run_resource
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:54:38.750861+00:00
-- url     : https://prove2.me/submissions/78118137-0321-4bd6-aa00-4dfc53b4815b

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
open QEC.Distillation.AdaptiveIdealClifford.DeterministicStep
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Wire : Type} [Fintype Wire] {Token : Type}
variable {presentation : CliffordPresentation (H := QubitRegister ι) Wire}
namespace QEC.Distillation.AdaptiveIdealClifford.DeterministicStep
theorem _root_.solution
    (use : ResourceUse (H := QubitRegister ι) (K := QubitRegister ι)
      (R := QubitSpace) Token)
    (rho : DensityOperator (QubitRegister ι)) :
    (DeterministicStep.resource (presentation := presentation) use).run rho =
      use.run rho :=
  rfl
end QEC.Distillation.AdaptiveIdealClifford.DeterministicStep
