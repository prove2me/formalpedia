-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.BPTMeasurementDistance.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:31:20.898938+00:00
-- url     : https://prove2.me/submissions/8631ccf7-2ad7-4d6d-aa6f-9f149ff13b4c

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance

set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.QuditSubsystem
open scoped BigOperators
universe u
variable {J : Type u} [Fintype J] [DecidableEq J] (q : J → Nat)
namespace QEC.Semantics.QuditSubsystem
namespace BPTMeasurementDistance
theorem _root_.solution {C : QuantumCode (Qudit.QuditRegister q)}
    {d e : Nat} (hd : BPTMeasurementDistance C d) (he : e ≤ d) :
    BPTMeasurementDistance C e := by
  intro S hS
  exact hd S (hS.trans_le he)
end BPTMeasurementDistance
end QEC.Semantics.QuditSubsystem
