-- Prove2me | solution 2 for QEC.Semantics.QuditSubsystem.extendLocal_operatorSupportedOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:01:46.821393+00:00
-- url     : https://prove2.me/submissions/64e669b1-f70b-4653-986a-2861437ea5fa

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q) (A : Operator S.selectedSystem) :
    S.OperatorSupportedOn (S.extendLocal A) :=
  ⟨A, rfl⟩
end QEC.Semantics.QuditSubsystem
