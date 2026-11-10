-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryDistance_source_integer_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:21:07.888331+00:00
-- url     : https://prove2.me/submissions/5caeb76b-7cc6-4a5a-9e41-9a3976284840

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryDistance
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryParameters
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodedCode_not_full_noInformation
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodedCode_measurementDistance
import Theorems.Thm_QEC_Semantics_QuditSubsystem_le_finiteMeasurementDistance


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter
open scoped BigOperators Topology
attribute [local instance] QEC.Distillation.Ngu24Binary._p2m_local_instance_6d70a6dbef_22
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (i : Nat) :
    f256QuditDistanceBound i ≤ binaryDistance i :=
  QuditSubsystem.le_finiteMeasurementDistance _ _ (binaryEncodedCode_not_full_noInformation i)
    (binaryEncodedCode_measurementDistance i)
end QEC.Distillation.Ngu24Binary
