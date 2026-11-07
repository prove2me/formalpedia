-- Prove2me | solution 1 for QEC.Coding.FiniteFieldPauli.cssQuantumCode_dimension_eq_card_cosets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:54:31.256958+00:00
-- url     : https://prove2.me/submissions/907d4193-fbf8-4bcd-98cd-ec03da939db0

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

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FiniteFieldPauli
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.FiniteFieldPauli
theorem _root_.solution (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier) :
    (cssQuantumCode xCode zCode).dimension =
      Fintype.card (AdmissibleCoset xCode zCode) := by
  exact Module.finrank_eq_card_basis (cssCosetBasis xCode zCode horth)
end QEC.Coding.FiniteFieldPauli
