-- Prove2me | solution 2 for QEC.Distillation.HH18Protocol.resourceDecodedRun_operation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:31:57.257136+00:00
-- url     : https://prove2.me/submissions/40c32cf5-bd3f-47d7-94d9-fb726b37e58a

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Decoder
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NormalizedRun

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instNormalizedRunClassicalDecidable
namespace QEC.Distillation.HH18Protocol
theorem _root_.solution
    (inputs : ResourceInput resourceCount QubitSpace) :
    (resourceDecodedRun inputs).operation = decodedOperation :=
  rfl
end QEC.Distillation.HH18Protocol
