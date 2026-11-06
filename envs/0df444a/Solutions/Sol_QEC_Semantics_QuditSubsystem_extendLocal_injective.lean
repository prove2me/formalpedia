-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.extendLocal_injective
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:31:16.685108+00:00
-- url     : https://prove2.me/submissions/f7895a9d-2198-4594-9b27-89d5b07a1066

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

theorem solution (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) :
    Function.Injective S.extendLocal := by
  intro A B h
  have hrestricted := congrArg (S.restrictLocal hq) h
  simpa only [S.restrictLocal_extendLocal] using hrestricted
