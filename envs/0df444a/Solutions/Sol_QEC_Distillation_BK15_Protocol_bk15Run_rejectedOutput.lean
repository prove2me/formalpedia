-- Prove2me | solution 1 for QEC.Distillation.BK15.Protocol.bk15Run_rejectedOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T02:07:22.754386+00:00
-- url     : https://prove2.me/submissions/8edcb9c2-534a-400a-9929-01ae88a809f7

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_FifteenQubitH_Protocol

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Protocol
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput
open scoped BigOperators TensorProduct
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.BK15.Protocol
theorem _root_.solution (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) :
    (bk15Run epsilon hpositive).rejectedOutput =
      qubitEndpointConditional epsilon .rejected
        (rejected_endpointWeight_pos epsilon hpositive) := by
  rfl
end QEC.Distillation.BK15.Protocol
