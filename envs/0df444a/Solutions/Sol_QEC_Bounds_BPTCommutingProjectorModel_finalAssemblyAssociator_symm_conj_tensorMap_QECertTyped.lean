-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyAssociator_symm_conj_tensorMap_QECertTyped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T01:09:44.123935+00:00
-- url     : https://prove2.me/submissions/36878b70-8747-402b-99d5-2c36ccbe20e1

import Definitions.Def_QEC_Import_Typed_2435cb85c2937e18
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_symm_conj_tensorMap
set_option autoImplicit false
noncomputable section
open QEC QEC.Bounds
open scoped TensorProduct
universe v
open QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyAssociator_symm_conj_tensorMap_QECertTypedStatement.{v} := by
  intro L kappa inst M region nB nC hB hC WB WC
  dsimp only
  intro A0
  apply tensorAssociatorUnitary_symm_conj_tensorMap
