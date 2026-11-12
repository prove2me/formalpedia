-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.outputTraceError_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:40:48.764795+00:00
-- url     : https://prove2.me/submissions/ade8ae1c-4400-4884-a332-6b2d5a5539b4

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Decoder
import Theorems.Thm_QEC_Semantics_traceNorm_nonneg


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {m w : Nat}
    (rho sigma : DensityOperator (LogicalRegister m w)) :
    0 ≤ outputTraceError rho sigma :=
  traceNorm_nonneg _
end QEC.Distillation.HH18Parameterized
