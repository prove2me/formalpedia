-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryEncodedCode_carrier_le_cssCarrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:12:27.630576+00:00
-- url     : https://prove2.me/submissions/953d3eea-d098-43a6-b15a-b9e6bcb0e4cf

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCSS
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodedCode_basis_eq_coset
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryCosetKet_mem_cssCarrier

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
attribute [local instance] QEC.Distillation.Ngu24Binary.binaryCSSFieldWordFintype
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (i : Nat) :
    (binaryEncodedCode i).code.carrier ≤ (binaryCSSCode i).stabilizer.code.carrier := by
  rintro x ⟨u, rfl⟩
  let B := EuclideanSpace.basisFun (Word (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) Complex
  change (binaryEncodingIsometry i).toLinearMap u ∈ _
  rw [← B.sum_repr u]
  erw [map_sum]
  apply Submodule.sum_mem
  intro a _
  erw [map_smul]
  apply Submodule.smul_mem
  change (binaryEncodedCode i).encode (EuclideanSpace.basisFun _ Complex a) ∈ _
  rw [binaryEncodedCode_basis_eq_coset]
  exact binaryCosetKet_mem_cssCarrier i a
end QEC.Distillation.Ngu24Binary
