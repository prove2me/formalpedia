-- Prove2me | solution 2 for QEC.Semantics.QuditSubsystem.BPTMeasurementDistance.noInformationOn_of_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:19:45.265148+00:00
-- url     : https://prove2.me/submissions/f0b257d7-b8a1-44ac-8d29-209a7db5a5ee

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
namespace QEC.Semantics.QuditSubsystem
namespace BPTMeasurementDistance
theorem _root_.solution
    {C : QuantumCode (Qudit.QuditRegister q)} {d : Nat}
    (hDistance : BPTMeasurementDistance C d) (S : QuditSubsystem q)
    (hcard : Fintype.card S.SelectedCoordinates < d) :
    NoInformationOn C S :=
  hDistance S hcard
end BPTMeasurementDistance
end QEC.Semantics.QuditSubsystem
