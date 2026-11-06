-- Prove2me | solution 1 for QEC.Locality.localPauliTwirl_eq_refill_comp_erasureFromRegister
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:00:03.6918+00:00
-- url     : https://prove2.me/submissions/345abc15-8ece-4ad5-a037-ea395d1d00a0

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Theorems.Thm_QEC_Locality_wordPauliTwirlFactorized_eq_refill_comp_erasure
import Theorems.Thm_QEC_Locality_localPauliTwirl_eq_transport
import Theorems.Thm_QEC_Locality_quantumChannel_comp_assoc

set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution (S : FiniteSubsystem ι) :
    localPauliTwirl S =
      QuantumChannel.comp (localPauliRefill S) S.erasureChannelFromRegister := by
  rw [localPauliTwirl_eq_transport,
    wordPauliTwirlFactorized_eq_refill_comp_erasure]
  unfold localPauliRefill FiniteSubsystem.erasureChannelFromRegister
  exact (quantumChannel_comp_assoc
    (QuantumChannel.unitaryConj S.registerFactorization)
    S.erasureChannel
    (QuantumChannel.comp (QuantumChannel.unitaryConj S.registerFactorization.symm)
      (refillFactorized S))).symm
end QEC.Locality
