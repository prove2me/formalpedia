-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.erasureChannelFromRegister_rankOne_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:19:45.910124+00:00
-- url     : https://prove2.me/submissions/13f50397-4f64-4195-9828-5cc12131b53a

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Theorems.Thm_QEC_Semantics_QuditSubsystem_partialTraceRightRaw_rankOne_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorization_apply_basis
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
    (x y : Qudit.Label q) :
    S.erasureChannelFromRegister
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Qudit.Label q) Complex x)
          (EuclideanSpace.basisFun (Qudit.Label q) Complex y)).toLinearMap =
      (inner Complex
        (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex (S.splitLabel y).1)
        (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex (S.splitLabel x).1)) •
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex (S.splitLabel x).2)
          (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex (S.splitLabel y).2)).toLinearMap := by
  simp only [erasureChannelFromRegister, erasureChannel, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply]
  rw [conjOperator_rankOne S.registerFactorization]
  rw [S.registerFactorization_apply_basis x, S.registerFactorization_apply_basis y]
  rw [conjOperator_rankOne S.factorSwap]
  simp only [S.factorSwap_apply_tmul]
  change partialTraceRightRaw S.complementSystem S.selectedSystem _ = _
  rw [partialTraceRightRaw_rankOne_tmul]
end QEC.Semantics.QuditSubsystem
