-- Prove2me | solution 1 for QEC.Semantics.FiniteSubsystem.extendLocal_injective
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:00:27.397777+00:00
-- url     : https://prove2.me/submissions/00d7a6dc-7748-4999-b8a3-c7d9b7a513fd

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

theorem solution (S : FiniteSubsystem ι) : Function.Injective S.extendLocal := by
  exact Function.LeftInverse.injective
    (fun A : Operator S.selectedSystem => S.restrictLocal_extendLocal A)
