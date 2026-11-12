-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.resourceDecodedRun_operation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:27:40.844206+00:00
-- url     : https://prove2.me/submissions/0b4b94d2-ac49-4e49-9036-24c90a1c75a6

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
namespace QEC.Distillation.Triorthogonal.BH12Protocol
theorem _root_.solution (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace) :
    (resourceDecodedRun q inputs).operation = decodedOperation q :=
  rfl
end QEC.Distillation.Triorthogonal.BH12Protocol
