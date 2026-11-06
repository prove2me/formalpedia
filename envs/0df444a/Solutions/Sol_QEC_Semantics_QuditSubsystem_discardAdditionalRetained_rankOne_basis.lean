-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.discardAdditionalRetained_rankOne_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:46:13.3727+00:00
-- url     : https://prove2.me/submissions/45ac7f4b-1d98-4f37-bdc9-1a4e560dbe44

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Theorems.Thm_QEC_Semantics_QuditSubsystem_partialTraceRightRaw_rankOne_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
import Theorems.Thm_QEC_Semantics_QuditSubsystem_complementFactorization_apply_basis
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S T : QuditSubsystem q)
    (hST : S.selected ⊆ T.selected) (x y : Qudit.Label S.complementDimensions) :
    S.discardAdditionalRetained T hST
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex x)
          (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex y)).toLinearMap =
      (inner Complex
        (EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex
          (S.splitComplementLabel T hST y).1)
        (EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex
          (S.splitComplementLabel T hST x).1)) •
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex
            (S.splitComplementLabel T hST x).2)
          (EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex
            (S.splitComplementLabel T hST y).2)).toLinearMap := by
  simp only [discardAdditionalRetained, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply]
  rw [conjOperator_rankOne (S.complementFactorization T hST)]
  rw [S.complementFactorization_apply_basis T hST x,
    S.complementFactorization_apply_basis T hST y]
  rw [conjOperator_rankOne (S.additionalRetainedFactorSwap T)]
  simp only [S.additionalRetainedFactorSwap_apply_tmul]
  change partialTraceRightRaw T.complementSystem (S.additionalRetainedSystem T) _ = _
  rw [partialTraceRightRaw_rankOne_tmul]
end QEC.Semantics.QuditSubsystem
