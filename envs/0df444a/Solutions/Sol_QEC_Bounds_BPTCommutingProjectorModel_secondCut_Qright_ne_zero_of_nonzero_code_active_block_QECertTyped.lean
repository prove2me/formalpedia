-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCut_Qright_ne_zero_of_nonzero_code_active_block_QECertTyped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T19:06:07.683786+00:00
-- url     : https://prove2.me/submissions/d2cbb598-a425-4ac9-8f3a-bd658e66d0fe

import Definitions.Def_QEC_Import_Typed_44ce6a6af9c3191a
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_compressed_overlap_block_product_QECertChecked
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCodeLift_active_compression_ne_zero_of_nonzero_code_QECertChecked



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
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.secondCut_Qright_ne_zero_of_nonzero_code_active_block_QECertTypedStatement.{v} := by
  intro L kappa inst M region hcode component n hN W U Pleft Qright hactive hleft hright
  let A := M.fourFactorA region
  let H := component.1.restrictScalars Complex
  let N := isotypicLiftedMultiplicity.{0} n
  let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
  let J := tensorTripleSubtypeEmbedding (A := A) (C := CD) H
  let R := M.secondCutCodeLift region
  let Rcompressed : Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem A H) CD) :=
    (LinearMap.adjoint J).comp (R.comp J)
  let T := isotypicSectorBlockTransportLeft A H (W.restrictScalars Complex) N CD U
  have hcompressed_ne_zero : Rcompressed ≠ 0 :=
    @QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift_active_compression_ne_zero_of_nonzero_code_QECertChecked.{v}
      L kappa inst M region hcode component hactive
  have hblock : T.conjOperator Rcompressed = TensorProduct.map Pleft Qright :=
    @QEC.Bounds.BPTCommutingProjectorModel.secondCut_compressed_overlap_block_product_QECertChecked.{v}
      L kappa inst M region component n hN W U Pleft Qright hleft hright
  intro hzero
  have htransportedZero : T.conjOperator Rcompressed = 0 := by
    calc
      T.conjOperator Rcompressed = TensorProduct.map Pleft Qright := hblock
      _ = TensorProduct.map Pleft 0 := congrArg (TensorProduct.map Pleft) hzero
      _ = 0 := TensorProduct.map_zero_right Pleft
  have hcompressedZero : Rcompressed = 0 := by
    calc
      Rcompressed = T.symm.conjOperator (T.conjOperator Rcompressed) :=
        (T.symm_conjOperator_conjOperator Rcompressed).symm
      _ = T.symm.conjOperator 0 := congrArg T.symm.conjOperator htransportedZero
      _ = 0 := by
        simp only [Semantics.UnitaryTransport.conjOperator, LinearMap.zero_comp, LinearMap.comp_zero]
  exact hcompressed_ne_zero hcompressedZero
end QEC.Bounds.BPTCommutingProjectorModel
