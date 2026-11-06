-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.erasureRecoverableFromRegister_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:59:34.101232+00:00
-- url     : https://prove2.me/submissions/29ac23f4-fbb9-451c-83cb-740feb76c423

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Theorems.Thm_QEC_Semantics_QuditSubsystem_discardAdditionalRetained_erasureChannelFromRegister_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply



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
    (hST : S.selected ⊆ T.selected) (C : QuantumCode (Qudit.QuditRegister q)) :
    T.ErasureRecoverableFromRegister C → S.ErasureRecoverableFromRegister C := by
  rintro ⟨recovery, hRecovery⟩
  refine ⟨QuantumChannel.comp recovery (S.discardAdditionalRetained T hST), ?_⟩
  change Correctable (Qudit.QuditRegister q) S.complementSystem C
    S.erasureChannelFromRegister (QuantumChannel.comp recovery (S.discardAdditionalRetained T hST))
  change Correctable (Qudit.QuditRegister q) T.complementSystem C
    T.erasureChannelFromRegister recovery at hRecovery
  intro rho hSupported
  rw [QuantumChannel.comp_apply]
  rw [S.discardAdditionalRetained_erasureChannelFromRegister_apply T hST]
  exact hRecovery rho hSupported
end QEC.Semantics.QuditSubsystem
