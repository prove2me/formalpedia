-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyOutputEmbedding_eq_compressionCoordinateEmbedding_QECertTyped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:29:17.772554+00:00
-- url     : https://prove2.me/submissions/6614a49e-689d-4a24-b6f8-129ffc743f43

import Definitions.Def_QEC_Import_Typed_251dd49ccc7224dd
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_CompressionExteriorCoordinates
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyInputEmbedding_eq_compressionCoordinateEmbedding_QECertTyped
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyInputEmbedding_eq_outputEmbedding_QECertTyped


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyOutputEmbedding_eq_compressionCoordinateEmbedding_QECertTypedStatement.{v} := by
  intro L kappa inst M region bcomponent ccomponent nB nC hNB hNC WB WC UB UC
  have hOutput := @QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyInputEmbedding_eq_outputEmbedding_QECertTyped.{v}
    L kappa inst M region bcomponent ccomponent nB nC hNB hNC WB WC UB UC
  have hCoordinate := @QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyInputEmbedding_eq_compressionCoordinateEmbedding_QECertTyped.{v}
    L kappa inst M region bcomponent ccomponent nB nC hNB hNC WB WC UB UC
  refine Eq.trans (Eq.symm hOutput) ?_
  exact hCoordinate
end QEC.Bounds.BPTCommutingProjectorModel
