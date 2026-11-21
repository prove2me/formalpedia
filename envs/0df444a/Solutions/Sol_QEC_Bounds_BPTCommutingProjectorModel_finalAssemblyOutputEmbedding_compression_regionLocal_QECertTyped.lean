-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyOutputEmbedding_compression_regionLocal_QECertTyped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:04:39.325184+00:00
-- url     : https://prove2.me/submissions/1e6f7170-6456-4979-b1a4-48f0f9ad1cd8

import Definitions.Def_QEC_Import_Typed_c1e7bfc0f1b5a099
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyOutputEmbedding_eq_twoTransport_QECertTyped
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblySelectedTensor_compression_regionLocal_QECertTyped
import Theorems.Thm_QEC_Bounds_compression_conj_after_transportPair_of_eq



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
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyOutputEmbedding_compression_regionLocal_QECertTypedStatement.{v} := by
  intro L kappa inst M region bcomponent ccomponent nB nC hNB hNC WB WC UB UC A
  dsimp only
  let F := M.fourFactorTransport region
  let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
  let N := isotypicLiftedMultiplicity.{0} nB
  let X := WC.restrictScalars Complex
  let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
    (M.fourFactorD region)
  let E := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
  let eSel := (M.activeSelectedEmbedding region bcomponent WB UB).toLinearMap
  let eComp := (M.activeComplementEmbedding region ccomponent WC UC).toLinearMap
  let J := TensorProduct.map eSel eComp
  let R := M.regionSubsystem region
  let A0 : Semantics.Operator (Semantics.CompositeSystem S N) :=
    (LinearMap.adjoint eSel).comp (A.comp eSel)
  have hCoordinates := @QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyOutputEmbedding_eq_twoTransport_QECertTyped.{v}
    L kappa inst M region bcomponent ccomponent nB nC hNB hNC WB WC UB UC
  calc
    (LinearMap.adjoint E).comp ((F.conjOperator (R.extendLocalToRegister A)).comp E) =
      (LinearMap.adjoint J).comp
        ((R.registerFactorization.conjOperator (R.extendLocalToRegister A)).comp J) := by
          apply compression_conj_after_transportPair_of_eq
            F R.registerFactorization J E (R.extendLocalToRegister A)
          exact hCoordinates
    _ = TensorProduct.map A0
        (1 : Semantics.Operator (Semantics.CompositeSystem X D)) := by
          exact @QEC.Bounds.BPTCommutingProjectorModel.finalAssemblySelectedTensor_compression_regionLocal_QECertTyped.{v}
            L kappa inst M region bcomponent ccomponent nB nC hNB hNC WB WC UB UC A J rfl
end QEC.Bounds.BPTCommutingProjectorModel
