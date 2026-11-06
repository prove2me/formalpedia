-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.noInformationOn_of_carrier_eq_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:18:30.761538+00:00
-- url     : https://prove2.me/submissions/91a2dd66-1e65-42f8-af9b-93abb1204fe9

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_scalarCompression_of_carrier_eq_span_singleton

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
theorem _root_.solution
    (C : QuantumCode (Qudit.QuditRegister q)) (S : QuditSubsystem q)
    (v : Qudit.QuditRegister q) (hv : v ≠ 0) (hC : C.carrier = Complex ∙ v) :
    NoInformationOn C S := by
  intro E _
  exact scalarCompression_of_carrier_eq_span_singleton C v hv hC
    (S.extendLocalToRegister E)
end QEC.Semantics.QuditSubsystem
