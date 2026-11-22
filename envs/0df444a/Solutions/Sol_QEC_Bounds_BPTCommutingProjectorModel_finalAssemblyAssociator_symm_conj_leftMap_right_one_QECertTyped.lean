-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyAssociator_symm_conj_leftMap_right_one_QECertTyped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T01:57:16.063913+00:00
-- url     : https://prove2.me/submissions/7b0fdf39-648e-40db-b174-1bac8ce9d1f4

import Definitions.Def_QEC_Import_Typed_8e968132ef42b4f0
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyAssociator_symm_conj_tensorMap_QECertTyped
set_option autoImplicit false
noncomputable section
open QEC QEC.Bounds
open scoped TensorProduct
universe v
open QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyAssociator_symm_conj_leftMap_right_one_QECertTypedStatement.{v} := by
  intro L kappa inst M region nB nC hB hC WB WC
  dsimp only
  intro A0
  let X := WC.restrictScalars Complex
  let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
    (M.fourFactorD region)
  have hOne : TensorProduct.map (1 : Semantics.Operator X) (1 : Semantics.Operator D) =
      (1 : Semantics.Operator (Semantics.CompositeSystem X D)) := TensorProduct.map_one
  have hAssoc := M.finalAssemblyAssociator_symm_conj_tensorMap_QECertTyped
    (nB := nB) (nC := nC) region WB WC A0
  exact (congrArg
    (fun Q => (tensorAssociatorUnitary
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
        (isotypicLiftedMultiplicity.{0} nB)) X D).symm.conjOperator
        (TensorProduct.map A0 Q)) hOne).symm.trans hAssoc
