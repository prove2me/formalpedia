-- Prove2me | solution 2 for QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisObservable_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:46:55.546997+00:00
-- url     : https://prove2.me/submissions/f30200f0-a2c2-4c34-a3c0-02082f1455fe

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Theorems.Thm_QEC_Semantics_Qubit_localX_adjoint


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
namespace QEC.Distillation.Triorthogonal.BH12Protocol
theorem _root_.solution {q : Nat} (a : OddRow q) :
    LinearMap.adjoint (logicalABasisObservable a) =
      logicalABasisObservable a := by
  rw [logicalABasisObservable, UnitaryTransport.conjOperator_adjoint,
    Qubit.localX_adjoint]
end QEC.Distillation.Triorthogonal.BH12Protocol
