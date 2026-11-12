-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.resourceDecodedRun_operation
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T18:33:18.019873+00:00
-- url     : https://prove2.me/submissions/d757f214-a09d-4867-8522-513ae160c18e

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

theorem solution
    (inputs : ResourceInput resourceCount QubitSpace) :
    (resourceDecodedRun inputs).operation = decodedOperation := rfl