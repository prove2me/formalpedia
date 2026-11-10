-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryDistance_fails_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:02:28.302523+00:00
-- url     : https://prove2.me/submissions/c5a2a5d5-422d-4e29-8bae-13b6faba3c74

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryDistance
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryParameters
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodedCode_not_full_noInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_finiteMeasurementDistance_fails_succ


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
    ¬ QuditSubsystem.BPTMeasurementDistance (binaryEncodedCode i).code (binaryDistance i + 1) :=
  QuditSubsystem.finiteMeasurementDistance_fails_succ _ _
    (binaryEncodedCode_not_full_noInformation i)
end QEC.Distillation.Ngu24Binary
