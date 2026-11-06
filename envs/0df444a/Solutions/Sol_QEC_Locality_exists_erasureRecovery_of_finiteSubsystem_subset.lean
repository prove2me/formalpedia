-- Prove2me | solution 1 for QEC.Locality.exists_erasureRecovery_of_finiteSubsystem_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:21:18.646808+00:00
-- url     : https://prove2.me/submissions/d734dfa0-985b-47b5-bac5-cc7eb0b24545

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Theorems.Thm_QEC_Locality_exists_qudit_erasureRecovery_of_subset


set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution
    (S T : FiniteSubsystem ι) (hST : S.selected ⊆ T.selected)
    (C : QuantumCode (Qubit.QubitRegister ι))
    (hRecovery : ∃ recovery : QuantumChannel T.complementSystem (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) T.complementSystem C
        T.erasureChannelFromRegister recovery) :
    ∃ recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) S.complementSystem C
        S.erasureChannelFromRegister recovery := by
  exact
    (exists_qudit_erasureRecovery_of_subset
      (quditSubsystemOfFinite S) (quditSubsystemOfFinite T) hST C hRecovery)
end QEC.Locality
