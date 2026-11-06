-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.extendLocalToRegister_operatorSupportedOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:45:27.475099+00:00
-- url     : https://prove2.me/submissions/ac8af49b-d81d-4dea-833e-3fd8bf5accf0

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
theorem _root_.solution (S : QuditSubsystem q)
    (A : Operator S.selectedSystem) :
    S.OperatorSupportedOnRegister (S.extendLocalToRegister A) :=
  ⟨A, rfl⟩
end QEC.Semantics.QuditSubsystem
