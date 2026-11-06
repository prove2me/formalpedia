-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.registerFactorization_symm_apply_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:01:33.397024+00:00
-- url     : https://prove2.me/submissions/763b3518-e2f0-4349-8770-175bcae3abe0

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorization_apply_basis
import Theorems.Thm_QEC_Semantics_QuditSubsystem_split_recombineLabel
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
theorem _root_.solution (S : QuditSubsystem q)
    (labels : Qudit.Label S.selectedDimensions × Qudit.Label S.complementDimensions) :
    S.registerFactorization.symm
        ((EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex labels.1) ⊗ₜ[Complex]
          (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex labels.2)) =
      EuclideanSpace.basisFun (Qudit.Label q) Complex (S.recombineLabel labels) := by
  apply S.registerFactorization.toLinearEquiv.injective
  simp only [UnitaryTransport.symm]
  rw [S.registerFactorization.toLinearEquiv.apply_symm_apply]
  rw [S.registerFactorization_apply_basis]
  simp [S.split_recombineLabel]
end QEC.Semantics.QuditSubsystem
