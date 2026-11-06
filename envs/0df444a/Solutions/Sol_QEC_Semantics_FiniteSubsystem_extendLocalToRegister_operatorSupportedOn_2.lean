-- Prove2me | solution 2 for QEC.Semantics.FiniteSubsystem.extendLocalToRegister_operatorSupportedOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:58:45.176609+00:00
-- url     : https://prove2.me/submissions/ca5befab-e5b8-4c47-8ecc-31ea7c17619a

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
namespace QEC.Semantics.FiniteSubsystem
theorem _root_.solution (S : FiniteSubsystem ι)
    (A : Operator S.selectedSystem) :
    S.OperatorSupportedOnRegister (S.extendLocalToRegister A) :=
  ⟨A, rfl⟩
end QEC.Semantics.FiniteSubsystem
