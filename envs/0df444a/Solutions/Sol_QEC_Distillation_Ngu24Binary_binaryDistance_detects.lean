-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryDistance_detects
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:02:18.2058+00:00
-- url     : https://prove2.me/submissions/1fb49bfe-a156-4d1a-ac7c-88f845f96ac9

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryDistance
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryParameters
import Theorems.Thm_QEC_Semantics_QuditSubsystem_finiteMeasurementDistance_detects


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
    QuditSubsystem.BPTMeasurementDistance (binaryEncodedCode i).code (binaryDistance i) :=
  QuditSubsystem.finiteMeasurementDistance_detects _ _
end QEC.Distillation.Ngu24Binary
