-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.exists_recovery_replacementAfterErasure_iff_exists_recovery_erasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:18:19.792674+00:00
-- url     : https://prove2.me/submissions/b72e808e-67c0-4688-8c87-6bb962c5f0e8

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Theorems.Thm_QEC_Semantics_QuditSubsystem_exists_recovery_replacementAfterErasureWith_iff_exists_recovery_erasure
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



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
    (S : QuditSubsystem q) (hq : ∀ i, 0 < q i)
    (C : QuantumCode (Qudit.QuditRegister q)) :
    (∃ replacementRecovery : QuantumChannel (Qudit.QuditRegister q) (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) (Qudit.QuditRegister q) C
        (S.replacementAfterErasure hq) replacementRecovery) ↔
    (∃ erasureRecovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) S.complementSystem C
        S.erasureChannelFromRegister erasureRecovery) := by
  simpa [replacementAfterErasure] using
    S.exists_recovery_replacementAfterErasureWith_iff_exists_recovery_erasure
      (S.maximallyMixedSelected hq) C
end QEC.Semantics.QuditSubsystem
