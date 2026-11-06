-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.replacementRecovery_transfers_to_erasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:51:33.503239+00:00
-- url     : https://prove2.me/submissions/4e348881-56ea-4478-a954-6feefb50aecc

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement

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
    (replacementRecovery : QuantumChannel (Qudit.QuditRegister q) (Qudit.QuditRegister q)) :
    Correctable (Qudit.QuditRegister q) (Qudit.QuditRegister q) C
      (S.replacementAfterErasureWith rho) replacementRecovery →
    Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister
      (QuantumChannel.comp replacementRecovery (S.prepareSelected rho)) := by
  intro h rhoGlobal hSupported
  change replacementRecovery
    (S.prepareSelected rho (S.erasureChannelFromRegister rhoGlobal.toOperator)) =
      rhoGlobal.toOperator
  exact h rhoGlobal hSupported
end QEC.Semantics.QuditSubsystem
