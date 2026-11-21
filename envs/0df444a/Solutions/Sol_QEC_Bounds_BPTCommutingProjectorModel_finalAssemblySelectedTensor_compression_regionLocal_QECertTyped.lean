-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.finalAssemblySelectedTensor_compression_regionLocal_QECertTyped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T01:38:39.011657+00:00
-- url     : https://prove2.me/submissions/4b51d634-a84b-4aaf-9c08-116546fa5fbc

import Definitions.Def_QEC_Import_Typed_fad7a53b486a4f25
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_activeComplementEmbedding_adjoint_comp_self_QECertTyped
import Theorems.Thm_QEC_Bounds_registerFactorizedTensor_compression_left_of_embedding



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblySelectedTensor_compression_regionLocal_QECertTypedStatement.{v} := by
  intro L kappa inst M region bcomponent ccomponent nB nC hNB hNC WB WC UB UC A
  dsimp only
  intro J hJ
  let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
  let N := isotypicLiftedMultiplicity.{0} nB
  let X := WC.restrictScalars Complex
  let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
    (M.fourFactorD region)
  let H := Semantics.CompositeSystem S N
  let K := Semantics.CompositeSystem X D
  let eSel := (M.activeSelectedEmbedding region bcomponent WB UB).toLinearMap
  let eComp := (M.activeComplementEmbedding region ccomponent WC UC).toLinearMap
  let R := M.regionSubsystem region
  have hComplementIsometry : (LinearMap.adjoint eComp).comp eComp =
      (1 : Semantics.Operator K) := by
    exact M.activeComplementEmbedding_adjoint_comp_self_QECertTyped region ccomponent WC UC
  apply registerFactorizedTensor_compression_left_of_embedding
    L.localDimension R eSel eComp J
  · exact hJ
  · exact hComplementIsometry
end QEC.Bounds.BPTCommutingProjectorModel
