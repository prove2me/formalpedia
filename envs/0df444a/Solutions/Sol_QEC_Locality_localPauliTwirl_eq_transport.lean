-- Prove2me | solution 1 for QEC.Locality.localPauliTwirl_eq_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:51:43.475712+00:00
-- url     : https://prove2.me/submissions/cedff630-22b4-4b0a-8645-d716ccface66

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Theorems.Thm_QEC_Locality_unitaryTransport_toQuantumChannel

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
      QuantumChannel.comp (QuantumChannel.unitaryConj S.registerFactorization.symm)
        (QuantumChannel.comp (wordPauliTwirlFactorized S)
          (QuantumChannel.unitaryConj S.registerFactorization)) := by
  exact unitaryTransport_toQuantumChannel (wordPauliFamilyFactorized S)
    S.registerFactorization.symm S.registerFactorization.symm
    (wordPauliFamilyFactorized_complete S)
end QEC.Locality
