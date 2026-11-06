-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.adjoint_localEmbedding_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:45:11.985686+00:00
-- url     : https://prove2.me/submissions/c9609cc6-9a3a-4122-878e-0e3745204887

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
set_option maxHeartbeats 800000
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q) (hq : ∀ i, 0 < q i)
    (h : S.selectedSystem) (k : S.complementSystem) :
    LinearMap.adjoint (S.localEmbedding hq) (h ⊗ₜ[Complex] k) =
      (inner Complex (S.complementAnchor hq) k) • h := by
  apply (ext_iff_inner_left Complex).mpr
  intro x
  rw [LinearMap.adjoint_inner_right]
  simp [localEmbedding, TensorProduct.inner_tmul, inner_smul_right, mul_comm]
end QEC.Semantics.QuditSubsystem
