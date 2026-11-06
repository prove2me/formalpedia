-- Prove2me | solution 2 for QEC.Semantics.FiniteSubsystem.extendLocal_operatorSupportedOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:58:39.883605+00:00
-- url     : https://prove2.me/submissions/84587814-1a5e-4484-8fd9-766dfb415727

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
    S.OperatorSupportedOn (S.extendLocal A) :=
  ⟨A, rfl⟩
end QEC.Semantics.FiniteSubsystem
