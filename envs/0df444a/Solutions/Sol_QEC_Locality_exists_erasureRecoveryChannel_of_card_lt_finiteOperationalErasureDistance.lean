-- Prove2me | solution 1 for QEC.Locality.exists_erasureRecoveryChannel_of_card_lt_finiteOperationalErasureDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:24:19.214072+00:00
-- url     : https://prove2.me/submissions/3fdb6134-488e-4e1f-9338-83cba7646f12

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Locality_CorrectableRegions_OperationalErasureDistance
import Theorems.Thm_QEC_Locality_erasureRecoverableFromRegister_of_card_lt_finiteOperationalErasureDistance
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_erasureRecoverableFromRegister_iff_exists_correctable


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι))
    (S : Semantics.FiniteSubsystem ι) {d : Nat}
    (hDistance : d = finiteOperationalErasureDistance C)
    (hCard : S.selected.card < d) :
    ∃ recovery : Semantics.QuantumChannel S.complementSystem
        (Semantics.Qubit.QubitRegister ι),
      Semantics.Correctable (Semantics.Qubit.QubitRegister ι) S.complementSystem C
        S.erasureChannelFromRegister recovery := by
  subst d
  exact (S.erasureRecoverableFromRegister_iff_exists_correctable C).1
    (erasureRecoverableFromRegister_of_card_lt_finiteOperationalErasureDistance C S hCard)
end QEC.Locality
