-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.partialTraceRightRaw_rankOne_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:11:30.596519+00:00
-- url     : https://prove2.me/submissions/9b3991ce-5d98-473d-a44c-7a2ba54cc318

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
theorem _root_.solution (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (h h' : H) (k k' : K) :
    partialTraceRightRaw H K
      (InnerProductSpace.rankOne Complex (h ⊗ₜ[Complex] k) (h' ⊗ₜ[Complex] k')).toLinearMap =
      (inner Complex k' k) • (InnerProductSpace.rankOne Complex h h').toLinearMap := by
  let fh : Module.Dual Complex H := (innerSL Complex h').toLinearMap
  let fk : Module.Dual Complex K := (innerSL Complex k').toLinearMap
  have hRank :
      (InnerProductSpace.rankOne Complex (h ⊗ₜ[Complex] k) (h' ⊗ₜ[Complex] k')).toLinearMap =
        dualTensorHom Complex (CompositeSystem H K) (CompositeSystem H K)
          ((TensorProduct.dualDistribEquiv Complex H K) (fh ⊗ₜ[Complex] fk) ⊗ₜ[Complex]
            (h ⊗ₜ[Complex] k)) := by
    ext z
    simp [fh, fk, InnerProductSpace.rankOne_apply, dualTensorHom_apply,
      TensorProduct.dualDistribEquiv, TensorProduct.inner_tmul, mul_smul]
  rw [hRank]
  ext x
  simp [partialTraceRightRaw, fh, fk, InnerProductSpace.rankOne_apply,
    LinearMap.comp_apply, dualTensorHom_apply]
end QEC.Semantics.QuditSubsystem
