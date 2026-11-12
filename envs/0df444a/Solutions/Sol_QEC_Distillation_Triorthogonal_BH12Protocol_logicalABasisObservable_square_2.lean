-- Prove2me | solution 2 for QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisObservable_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:47:24.690393+00:00
-- url     : https://prove2.me/submissions/14f477fa-813a-4d25-ba35-d7d0d74f9e58

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Theorems.Thm_QEC_Semantics_Qubit_localX_square


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
    logicalABasisObservable a * logicalABasisObservable a = 1 := by
  rw [logicalABasisObservable, ← UnitaryTransport.conjOperator_mul,
    Qubit.localX_square]
  exact (allSiteT (Index := OddRow q)).conjOperator_one
end QEC.Distillation.Triorthogonal.BH12Protocol
