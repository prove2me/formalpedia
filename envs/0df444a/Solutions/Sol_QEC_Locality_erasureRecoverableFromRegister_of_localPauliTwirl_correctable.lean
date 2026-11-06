-- Prove2me | solution 1 for QEC.Locality.erasureRecoverableFromRegister_of_localPauliTwirl_correctable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:02:36.563148+00:00
-- url     : https://prove2.me/submissions/6ed9f414-dc6d-4559-bda7-5d42c39c08b8

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Theorems.Thm_QEC_Locality_localPauliTwirl_eq_refill_comp_erasureFromRegister

set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (S : FiniteSubsystem ι) (C : QuantumCode (Qubit.QubitRegister ι))
    (recovery : QuantumChannel (Qubit.QubitRegister ι) (Qubit.QubitRegister ι))
    (h : Correctable (Qubit.QubitRegister ι) (Qubit.QubitRegister ι) C
      (localPauliTwirl S) recovery) :
    S.ErasureRecoverableFromRegister C := by
  refine ⟨QuantumChannel.comp recovery (localPauliRefill S), ?_⟩
  intro rho hrho
  have hcorrected := h rho hrho
  change recovery (localPauliRefill S (S.erasureChannelFromRegister rho.toOperator)) =
    rho.toOperator
  have hnoise := congrArg
    (fun Phi : QuantumChannel (Qubit.QubitRegister ι) (Qubit.QubitRegister ι) =>
      Phi rho.toOperator)
    (localPauliTwirl_eq_refill_comp_erasureFromRegister S)
  change (localPauliTwirl S) rho.toOperator =
    localPauliRefill S (S.erasureChannelFromRegister rho.toOperator) at hnoise
  rw [← hnoise]
  exact hcorrected
end QEC.Locality
