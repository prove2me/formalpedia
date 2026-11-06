-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.discardAdditionalRetained_erasureChannelFromRegister_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:57:20.804116+00:00
-- url     : https://prove2.me/submissions/af8b5098-f8f9-4528-ae12-9e2393969d68

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Theorems.Thm_QEC_Semantics_QuditSubsystem_linearMap_ext_of_rankOne_basis
import Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureChannelFromRegister_rankOne_basis
import Theorems.Thm_QEC_Semantics_QuditSubsystem_inner_selectedBasis_split
import Theorems.Thm_QEC_Semantics_QuditSubsystem_splitSelectedLabel_splitLabel
import Theorems.Thm_QEC_Semantics_QuditSubsystem_splitComplementLabel_splitLabel_second
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_discardAdditionalRetained_rankOne_basis
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
theorem _root_.solution
    (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected)
    (A : Operator (Qudit.QuditRegister q)) :
    S.discardAdditionalRetained T hST (S.erasureChannelFromRegister A) =
      T.erasureChannelFromRegister A := by
  let basis := EuclideanSpace.basisFun (Qudit.Label q) Complex
  let Phi : Operator (Qudit.QuditRegister q) →ₗ[Complex] Operator T.complementSystem :=
    (S.discardAdditionalRetained T hST).toLinearMap.comp S.erasureChannelFromRegister.toLinearMap
  let Psi : Operator (Qudit.QuditRegister q) →ₗ[Complex] Operator T.complementSystem :=
    T.erasureChannelFromRegister.toLinearMap
  have hMaps : Phi = Psi := by
    apply linearMap_ext_of_rankOne_basis basis Phi Psi
    intro x y
    dsimp [Phi, Psi]
    rw [S.erasureChannelFromRegister_rankOne_basis x y]
    rw [map_smul]
    rw [S.discardAdditionalRetained_rankOne_basis T hST (S.splitLabel x).2 (S.splitLabel y).2]
    rw [T.erasureChannelFromRegister_rankOne_basis x y]
    rw [S.inner_selectedBasis_split T hST (T.splitLabel x).1 (T.splitLabel y).1]
    simp only [S.splitSelectedLabel_splitLabel T hST,
      S.splitComplementLabel_splitLabel_second T hST]
    simp [smul_smul]
  exact DFunLike.congr_fun hMaps A
end QEC.Semantics.QuditSubsystem
