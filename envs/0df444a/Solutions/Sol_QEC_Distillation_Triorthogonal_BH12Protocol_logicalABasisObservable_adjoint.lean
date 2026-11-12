-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisObservable_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T19:20:01.30008+00:00
-- url     : https://prove2.me/submissions/f2891e50-ff75-45cb-ad9c-3fa21fc3a628

import Theorems.Thm_QEC_Semantics_Qubit_localX_adjoint
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
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

theorem solution {q : Nat} (a : OddRow q) :
    LinearMap.adjoint (logicalABasisObservable a) =
      logicalABasisObservable a := by
  rw [logicalABasisObservable, UnitaryTransport.conjOperator_adjoint,
    Qubit.localX_adjoint]