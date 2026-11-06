-- Prove2me | solution 1 for QEC.Semantics.FiniteSubsystem.operatorSupportedOnRegister_iff_extend_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:58:48.531165+00:00
-- url     : https://prove2.me/submissions/2b507ffe-fb29-4172-879c-ea3e27c8b445

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_restrictLocalFromRegister_extendLocalToRegister

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
open QEC.Semantics.FiniteSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.FiniteSubsystem
theorem _root_.solution (S : FiniteSubsystem ι)
    (A : Operator (Qubit.QubitRegister ι)) :
    S.OperatorSupportedOnRegister A ↔
      S.extendLocalToRegister (S.restrictLocalFromRegister A) = A := by
  constructor
  · rintro ⟨A_local, rfl⟩
    rw [S.restrictLocalFromRegister_extendLocalToRegister]
  · intro h
    exact ⟨S.restrictLocalFromRegister A, h⟩
end QEC.Semantics.FiniteSubsystem
