-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.operatorSupportedOnRegister_iff_extend_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:01:57.090122+00:00
-- url     : https://prove2.me/submissions/f1dedf2e-aa0b-4e3b-96e9-03057b10301f

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Theorems.Thm_QEC_Semantics_QuditSubsystem_restrictLocalFromRegister_extendLocalToRegister

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
    (hq : ∀ i, 0 < q i) (A : Operator (Qudit.QuditRegister q)) :
    S.OperatorSupportedOnRegister A ↔
      S.extendLocalToRegister (S.restrictLocalFromRegister hq A) = A := by
  constructor
  · rintro ⟨localOperator, rfl⟩
    rw [S.restrictLocalFromRegister_extendLocalToRegister]
  · intro h
    exact ⟨S.restrictLocalFromRegister hq A, h⟩
end QEC.Semantics.QuditSubsystem
