-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.noInformationOn_iff_exists_erasureRecovery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:59:08.492185+00:00
-- url     : https://prove2.me/submissions/6d944f65-5b54-4bb6-b616-f1d7367e7849

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_implies_erasureRecovery
import Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureRecovery_implies_noInformationOn

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
    (hq : ∀ i, 0 < q i) :
    NoInformationOn C S ↔
      ∃ recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q),
        Correctable (Qudit.QuditRegister q) S.complementSystem C
          S.erasureChannelFromRegister recovery := by
  let rho := S.maximallyMixedSelected hq
  constructor
  · intro hInformation
    exact S.noInformationOn_implies_erasureRecovery C rho hInformation
  · rintro ⟨recovery, hRecovery⟩
    exact S.erasureRecovery_implies_noInformationOn C rho recovery hRecovery
end QEC.Semantics.QuditSubsystem
