-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.operatorSupportedOn_iff_extend_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:01:53.325294+00:00
-- url     : https://prove2.me/submissions/66422be8-ed98-4c9a-bd10-7014dfbf3602

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Theorems.Thm_QEC_Semantics_QuditSubsystem_restrictLocal_extendLocal

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
theorem _root_.solution (S : QuditSubsystem q) (hq : ∀ i, 0 < q i)
    (A : Operator S.factorizedSystem) :
    S.OperatorSupportedOn A ↔ S.extendLocal (S.restrictLocal hq A) = A := by
  constructor
  · rintro ⟨localOperator, rfl⟩
    rw [S.restrictLocal_extendLocal]
  · intro h
    exact ⟨S.restrictLocal hq A, h⟩
end QEC.Semantics.QuditSubsystem
