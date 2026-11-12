-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18OutputTraceError_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:33:59.392025+00:00
-- url     : https://prove2.me/submissions/00d3c96c-a4d9-46b5-90d2-7822cc65d1bd

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalTypes
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Decoder
import Theorems.Thm_QEC_Semantics_traceNorm_nonneg


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
namespace QEC.Distillation.HH18Protocol
theorem _root_.solution
    (rho sigma : DensityOperator LogicalRegister) :
    0 ≤ hh18OutputTraceError rho sigma :=
  traceNorm_nonneg _
end QEC.Distillation.HH18Protocol
