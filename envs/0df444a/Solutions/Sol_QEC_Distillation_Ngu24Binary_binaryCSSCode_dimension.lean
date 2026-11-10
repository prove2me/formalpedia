-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryCSSCode_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:24:55.589542+00:00
-- url     : https://prove2.me/submissions/df289baf-0754-4220-9ff4-9f4878705cbd

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCSS
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryAmbientCode_dimension
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryXCode_dimension
import Theorems.Thm_QEC_Coding_LinearCode_dimension_add_dual_dimension_eq_length
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSQuantumCodeOfDualLe_finrank_carrier


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (i : Nat) :
    (binaryCSSCode i).stabilizer.code.dimension = 2 ^ f256MultiplicationLogicalCount i := by
  change Module.finrank Complex
    (PauliSymplectic.binaryCSSQuantumCodeOfDualLe (binaryXCode i) (binaryZCode i)
      (binaryZCode_le_xDual i)).carrier = _
  rw [PauliSymplectic.binaryCSSQuantumCodeOfDualLe_finrank_carrier]
  congr 1
  have h := (binaryAmbientCode i).dimension_add_dual_dimension_eq_length
  rw [binaryAmbientCode_dimension] at h
  rw [binaryXCode_dimension]
  change _ - _ - Dimension (binaryAmbientCode i).dual = _
  omega
end QEC.Distillation.Ngu24Binary
