-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.le_finiteMeasurementDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:20:11.812145+00:00
-- url     : https://prove2.me/submissions/e1f33f8d-525c-40de-a7ce-b82095111b80

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Theorems.Thm_QEC_Semantics_QuditSubsystem_BPTMeasurementDistance_mono
import Theorems.Thm_QEC_Semantics_QuditSubsystem_finiteMeasurementDistance_fails_succ

set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.QuditSubsystem
open scoped BigOperators
universe u
variable {J : Type u} [Fintype J] [DecidableEq J] (q : J → Nat)
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (C : QuantumCode (Qudit.QuditRegister q))
    (hfull : ¬ NoInformationOn C (fullRegion q)) {d : Nat}
    (hd : BPTMeasurementDistance C d) : d ≤ finiteMeasurementDistance q C := by
  by_contra h
  apply finiteMeasurementDistance_fails_succ q C hfull
  exact hd.mono q (by omega)
end QEC.Semantics.QuditSubsystem
