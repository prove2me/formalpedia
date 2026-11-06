-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.BPTMeasurementDistance.noInformationOn_of_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:52:12.12841+00:00
-- url     : https://prove2.me/submissions/8039f032-b3ce-4728-a66f-725a57c606b3

-- ID: 8f93cffa-75f3-4b1c-9246-d6923664879d | NAME: QEC.Semantics.QuditSubsystem.BPTMeasurementDistance.noInformationOn_of_card_lt | 未本地编译验证
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
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

theorem solution
    {C : QuantumCode (Qudit.QuditRegister q)} {d : Nat}
    (hDistance : BPTMeasurementDistance C d) (S : QuditSubsystem q)
    (hcard : Fintype.card S.SelectedCoordinates < d) :
    NoInformationOn C S := by
  exact hDistance S hcard
