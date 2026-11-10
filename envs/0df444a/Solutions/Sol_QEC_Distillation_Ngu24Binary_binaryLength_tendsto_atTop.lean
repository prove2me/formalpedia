-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryLength_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:04:19.376363+00:00
-- url     : https://prove2.me/submissions/fbe2bfdc-b48e-478b-9f3c-7504dbc1ef7b

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryDistance
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryParameters
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256QuditLength_tendsto_atTop


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter
open scoped BigOperators Topology
attribute [local instance] QEC.Distillation.Ngu24Binary._p2m_local_instance_6d70a6dbef_22
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution : Tendsto binaryLength atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [(tendsto_atTop.1 f256QuditLength_tendsto_atTop) b] with i hi
  unfold binaryLength
  omega
end QEC.Distillation.Ngu24Binary
