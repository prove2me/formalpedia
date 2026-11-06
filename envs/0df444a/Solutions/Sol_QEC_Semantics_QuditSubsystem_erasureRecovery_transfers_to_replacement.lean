-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.erasureRecovery_transfers_to_replacement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:25:29.971032+00:00
-- url     : https://prove2.me/submissions/8e358583-026e-4f64-8ca9-ab6b2bc3c6d0

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureChannelFromRegister_prepareSelected_apply

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
theorem _root_.solution (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) (C : QuantumCode (Qudit.QuditRegister q))
    (erasureRecovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q)) :
    Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister erasureRecovery →
    Correctable (Qudit.QuditRegister q) (Qudit.QuditRegister q) C
      (S.replacementAfterErasureWith rho)
      (QuantumChannel.comp erasureRecovery S.erasureChannelFromRegister) := by
  intro h rhoGlobal hSupported
  change erasureRecovery (S.erasureChannelFromRegister
    (S.prepareSelected rho (S.erasureChannelFromRegister rhoGlobal.toOperator))) =
      rhoGlobal.toOperator
  rw [S.erasureChannelFromRegister_prepareSelected_apply rho]
  exact h rhoGlobal hSupported
end QEC.Semantics.QuditSubsystem
