-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.complementFactorization_symm_apply_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:02:06.088513+00:00
-- url     : https://prove2.me/submissions/25c4ed42-1e6e-4593-a907-328af4352e7c

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Theorems.Thm_QEC_Semantics_QuditSubsystem_complementFactorization_apply_basis
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
theorem _root_.solution (S T : QuditSubsystem q)
    (hST : S.selected ⊆ T.selected)
    (labels : Qudit.Label (S.additionalRetainedDimensions T) × Qudit.Label T.complementDimensions) :
    (S.complementFactorization T hST).symm
        ((EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex labels.1)
          ⊗ₜ[Complex]
          (EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex labels.2)) =
      EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
        (S.recombineComplementLabel T labels) := by
  apply (S.complementFactorization T hST).toLinearEquiv.injective
  simp only [UnitaryTransport.symm]
  rw [(S.complementFactorization T hST).toLinearEquiv.apply_symm_apply]
  rw [S.complementFactorization_apply_basis T hST]
  have hlabels :
      S.splitComplementLabel T hST (S.recombineComplementLabel T labels) = labels := by
    exact (S.complementLabelFactorization T hST).right_inv labels
  rw [hlabels]
end QEC.Semantics.QuditSubsystem
