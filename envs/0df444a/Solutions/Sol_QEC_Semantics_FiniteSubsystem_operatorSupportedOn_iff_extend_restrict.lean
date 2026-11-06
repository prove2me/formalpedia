-- Prove2me | solution 1 for QEC.Semantics.FiniteSubsystem.operatorSupportedOn_iff_extend_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:58:47.53486+00:00
-- url     : https://prove2.me/submissions/ef86728c-6e1b-41eb-9423-cb8fdb6696da

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_restrictLocal_extendLocal

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
    (A : Operator S.factorizedSystem) :
    S.OperatorSupportedOn A ↔ S.extendLocal (S.restrictLocal A) = A := by
  constructor
  · rintro ⟨A_local, rfl⟩
    rw [S.restrictLocal_extendLocal]
  · intro h
    exact ⟨S.restrictLocal A, h⟩
end QEC.Semantics.FiniteSubsystem
