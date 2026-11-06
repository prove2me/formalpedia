-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.complementFactorization_apply_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:26:02.349841+00:00
-- url     : https://prove2.me/submissions/2d470514-519f-4f1d-8eab-cf2dab35edab

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
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
theorem _root_.solution (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected)
    (labels : Qudit.Label S.complementDimensions) :
    S.complementFactorization T hST
        (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex labels) =
      (EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex
        (S.splitComplementLabel T hST labels).1) ⊗ₜ[Complex]
      (EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex
        (S.splitComplementLabel T hST labels).2) := by
  dsimp [complementFactorization]
  rw [OrthonormalBasis.equiv_apply_basis]
  rw [OrthonormalBasis.tensorProduct_apply']
  simp [complementLabelFactorization]
end QEC.Semantics.QuditSubsystem
