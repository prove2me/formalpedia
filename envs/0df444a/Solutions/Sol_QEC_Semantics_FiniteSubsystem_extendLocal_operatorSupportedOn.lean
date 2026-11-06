-- Prove2me | solution 1 for QEC.Semantics.FiniteSubsystem.extendLocal_operatorSupportedOn
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:46:58.473227+00:00
-- url     : https://prove2.me/submissions/223535b6-aef7-46d1-84ac-298390268231

-- ID: 3ee85252-aff2-44c4-bb91-6b3ccf6c4830 | NAME: QEC.Semantics.FiniteSubsystem.extendLocal_operatorSupportedOn | 未本地编译验证
import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Core_Subsystem
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
open QEC.Semantics.FiniteSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem solution (S : FiniteSubsystem ι)
    (A : Operator S.selectedSystem) :
    S.OperatorSupportedOn (S.extendLocal A) := by
  exact ⟨A, rfl⟩
