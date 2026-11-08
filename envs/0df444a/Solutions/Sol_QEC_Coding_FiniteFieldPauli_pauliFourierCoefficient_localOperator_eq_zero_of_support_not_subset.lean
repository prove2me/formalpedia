-- Prove2me | solution 1 for QEC.Coding.FiniteFieldPauli.pauliFourierCoefficient_localOperator_eq_zero_of_support_not_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:08:05.703887+00:00
-- url     : https://prove2.me/submissions/54773031-501b-4efe-afc4-d5295c71982c

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Coding_QLDPC_BPTMeasurementDistance
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditMatrixElements
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.FieldTheory.Finiteness
import Mathlib.NumberTheory.LegendreSymbol.Complex
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_localFourierCoefficient_eq_zero_of_outside
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_pauliSupport_not_subset_iff_outside

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FiniteFieldPauli
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
set_option maxHeartbeats 1000000
namespace QEC.Coding.FiniteFieldPauli
theorem _root_.solution
    {ι' : Type u} [Fintype ι'] [DecidableEq ι'] [DecidableEq F]
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (E : Semantics.Operator S.selectedSystem)
    (x z : Word F ι') (houtside : ¬ pauliSupport x z ⊆ S.selected) :
    pauliFourierCoefficient (Semantics.FiniteAlphabet.localOperator S E) x z = 0 := by
  have houtside' := (pauliSupport_not_subset_iff_outside x z S.selected).mp houtside
  exact localFourierCoefficient_eq_zero_of_outside S E x z houtside'
end QEC.Coding.FiniteFieldPauli
