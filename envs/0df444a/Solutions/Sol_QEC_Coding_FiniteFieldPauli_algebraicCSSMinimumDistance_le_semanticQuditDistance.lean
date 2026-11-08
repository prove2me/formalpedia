-- Prove2me | solution 1 for QEC.Coding.FiniteFieldPauli.algebraicCSSMinimumDistance_le_semanticQuditDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:26:45.901373+00:00
-- url     : https://prove2.me/submissions/761ad634-b926-4c12-bc63-e5aab8db133d

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
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_cssQuditCode_bptMeasurementDistance_of_algebraicCSSMinimumDistance
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_cssQuditCode_not_noInformationOn_fullRegion
import Theorems.Thm_QEC_QLDPC_le_semanticQuditDistance_of_bptMeasurementDistance


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FiniteFieldPauli
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
set_option maxHeartbeats 1000000
namespace QEC.Coding.FiniteFieldPauli
theorem _root_.solution
    {ι' : Type u} [Fintype ι']
    (xCode zCode : LinearCode F ι')
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (d : Nat) (hminimum : AlgebraicCSSMinimumDistance xCode zCode d) :
    d ≤ QLDPC.semanticQuditDistance (fun _ : ι' => Fintype.card F)
      (cssQuditCode xCode zCode) := by
  exact QLDPC.le_semanticQuditDistance_of_bptMeasurementDistance
    (cssQuditCode xCode zCode) d
    (cssQuditCode_bptMeasurementDistance_of_algebraicCSSMinimumDistance
      xCode zCode horth d hminimum)
    (cssQuditCode_not_noInformationOn_fullRegion
      xCode zCode horth d hminimum)
end QEC.Coding.FiniteFieldPauli
