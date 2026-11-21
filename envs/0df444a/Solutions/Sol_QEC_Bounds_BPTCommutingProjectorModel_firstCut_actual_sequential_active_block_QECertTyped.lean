-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.firstCut_actual_sequential_active_block_QECertTyped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:28:50.330944+00:00
-- url     : https://prove2.me/submissions/bb1ed982-d2ee-46a3-a320-f804ab99c546

import Definitions.Def_QEC_Import_Typed_3d01c2d96213bf31
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_FirstCutCore
import Definitions.Def_QEC_Bounds_BPTDisentangling_FirstCutBlock
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveBlockTransports
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_Factors
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_FirstCutActiveData
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_FirstCutActive
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_compressed_overlap_block_product_QECertChecked
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_sequential_firstCut_named_block


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
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.firstCut_actual_sequential_active_block_QECertTypedStatement.{v} := by
  intro L kappa inst M region bcomponent ccomponent nB nC hNB hNC WB WC UB UC Pfirst P_D hleft hright
  unfold FirstCutActualSequentialActiveBlock
  have hblock := @QEC.Bounds.BPTCommutingProjectorModel.firstCut_compressed_overlap_block_product_QECertChecked.{v}
    L kappa inst M region ccomponent nC hNC WC UC Pfirst P_D hleft hright
  exact sequential_firstCut_named_block
      (A := M.fourFactorA region)
      (B := bcomponent.1.restrictScalars Complex)
      (B' := M.fourFactorB region)
      (H := ccomponent.1.restrictScalars Complex)
      (W := WC.restrictScalars Complex)
      (N := isotypicLiftedMultiplicity.{0} nC)
      (D := M.fourFactorD region)
      (WB := WB.restrictScalars Complex)
      (NB := isotypicLiftedMultiplicity.{0} nB)
      UC UB
      (bcomponent.1.restrictScalars Complex).subtype
      ((LinearMap.adjoint (tensorTripleSubtypeEmbedding
        (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (C := M.fourFactorD region) (ccomponent.1.restrictScalars Complex))).comp
        ((M.firstCutCodeLift region).comp
          (tensorTripleSubtypeEmbedding
            (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
            (C := M.fourFactorD region) (ccomponent.1.restrictScalars Complex))))
      Pfirst P_D
      (M.sequentialFirstCutJointCompression region
        (bcomponent.1.restrictScalars Complex) (ccomponent.1.restrictScalars Complex))
      (M.firstCutPleftOnSecondCutActiveSector region bcomponent WB UB
        (WC.restrictScalars Complex) Pfirst)
      (M.firstCutJointActiveBlockTransport region bcomponent ccomponent WB WC UB UC)
      rfl rfl rfl hblock
end QEC.Bounds.BPTCommutingProjectorModel
