-- Prove2me | solution 1 for QEC.Semantics.FiniteSubsystem.extendLocalToRegister_injective
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:29:49.459638+00:00
-- url     : https://prove2.me/submissions/df4e8785-06cd-4045-96b7-f2cbe2e5938a

import Theorems.Thm_QEC_Semantics_FiniteSubsystem_restrictLocalFromRegister_extendLocalToRegister
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

theorem solution (S : FiniteSubsystem ι) :
    Function.Injective S.extendLocalToRegister := by
  intro A B h
  have hrestricted := congrArg S.restrictLocalFromRegister h
  simpa only [S.restrictLocalFromRegister_extendLocalToRegister] using hrestricted
