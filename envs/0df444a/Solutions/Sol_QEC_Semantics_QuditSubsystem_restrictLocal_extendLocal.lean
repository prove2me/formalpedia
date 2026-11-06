-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.restrictLocal_extendLocal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:47:59.994144+00:00
-- url     : https://prove2.me/submissions/b63bf000-0fe6-4fad-b3d5-7b06e582dd9d

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Theorems.Thm_QEC_Semantics_QuditSubsystem_adjoint_localEmbedding_tmul
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
theorem _root_.solution (S : QuditSubsystem q) (hq : ∀ i, 0 < q i)
    (A : Operator S.selectedSystem) :
    S.restrictLocal hq (S.extendLocal A) = A := by
  apply LinearMap.ext
  intro h
  change LinearMap.adjoint (S.localEmbedding hq)
      (S.extendLocal A (S.localEmbedding hq h)) = A h
  rw [S.extendLocal_apply_localEmbedding hq, S.localEmbedding_apply,
    S.adjoint_localEmbedding_tmul]
  simp [complementAnchor]
end QEC.Semantics.QuditSubsystem
