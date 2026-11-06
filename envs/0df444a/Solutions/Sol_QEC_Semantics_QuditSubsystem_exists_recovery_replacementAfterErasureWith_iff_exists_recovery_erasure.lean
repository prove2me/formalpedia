-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.exists_recovery_replacementAfterErasureWith_iff_exists_recovery_erasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:28:44.040203+00:00
-- url     : https://prove2.me/submissions/abc3519c-ad61-4cbb-b853-8289783c5291

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementRecovery_transfers_to_erasure
import Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureRecovery_transfers_to_replacement

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.QuditSubsystem
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution
    (S : QuditSubsystem q) (rho : DensityOperator S.selectedSystem)
    (C : QuantumCode (Qudit.QuditRegister q)) :
    (∃ replacementRecovery : QuantumChannel (Qudit.QuditRegister q) (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) (Qudit.QuditRegister q) C
        (S.replacementAfterErasureWith rho) replacementRecovery) ↔
    (∃ erasureRecovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) S.complementSystem C
        S.erasureChannelFromRegister erasureRecovery) := by
  constructor
  · rintro ⟨replacementRecovery, hRecovery⟩
    exact ⟨QuantumChannel.comp replacementRecovery (S.prepareSelected rho),
      S.replacementRecovery_transfers_to_erasure rho C replacementRecovery hRecovery⟩
  · rintro ⟨erasureRecovery, hRecovery⟩
    exact ⟨QuantumChannel.comp erasureRecovery S.erasureChannelFromRegister,
      S.erasureRecovery_transfers_to_replacement rho C erasureRecovery hRecovery⟩
end QEC.Semantics.QuditSubsystem
