-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.finiteMeasurementDistance_fails_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:33:59.454201+00:00
-- url     : https://prove2.me/submissions/95d7c196-598c-49bf-ab11-a22d30b1c623

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Theorems.Thm_QEC_Semantics_QuditSubsystem_failedThreshold_nonempty

set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.QuditSubsystem
open scoped BigOperators
universe u
variable {J : Type u} [Fintype J] [DecidableEq J] (q : J → Nat)
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (C : QuantumCode (Qudit.QuditRegister q))
    (hfull : ¬ NoInformationOn C (fullRegion q)) :
    ¬ BPTMeasurementDistance C (finiteMeasurementDistance q C + 1) :=
  Nat.sInf_mem (failedThreshold_nonempty q C hfull)
end QEC.Semantics.QuditSubsystem
