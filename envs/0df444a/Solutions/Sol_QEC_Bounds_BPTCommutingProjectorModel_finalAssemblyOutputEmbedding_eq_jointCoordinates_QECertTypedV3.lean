-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyOutputEmbedding_eq_jointCoordinates_QECertTypedV3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T04:06:10.725462+00:00
-- url     : https://prove2.me/submissions/87e20a38-7332-448a-ac8b-a2c30cbe17aa

import Definitions.Def_QEC_Import_Typed_175b654756d58e31_V3

set_option autoImplicit false
noncomputable section
open QEC QEC.Bounds Classical
open scoped BigOperators ComplexOrder TensorProduct
universe v
open QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyOutputEmbedding_eq_jointCoordinates_QECertTypedStatementV3.{v} := by
  intro L kappa inst M region bcomponent ccomponent nB nC hB hC WB WC UB UC
  rfl
