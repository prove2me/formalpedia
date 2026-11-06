-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.noInformationOn_implies_erasureRecovery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:56:12.824141+00:00
-- url     : https://prove2.me/submissions/de8ac09e-6042-4351-8fca-020f701faa14

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_implies_replacementAfterErasureWith_recovery
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementRecovery_transfers_to_erasure


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
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (rho : DensityOperator S.selectedSystem)
    (hInformation : NoInformationOn C S) :
    ∃ recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) S.complementSystem C
        S.erasureChannelFromRegister recovery := by
  rcases S.noInformationOn_implies_replacementAfterErasureWith_recovery C rho hInformation
    with ⟨replacementRecovery, hReplacement⟩
  exact ⟨QuantumChannel.comp replacementRecovery (S.prepareSelected rho),
    S.replacementRecovery_transfers_to_erasure rho C replacementRecovery hReplacement⟩
end QEC.Semantics.QuditSubsystem
