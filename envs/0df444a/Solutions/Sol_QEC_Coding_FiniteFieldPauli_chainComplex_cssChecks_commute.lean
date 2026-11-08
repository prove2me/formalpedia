-- Prove2me | solution 1 for QEC.Coding.FiniteFieldPauli.chainComplex_cssChecks_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:26:11.876893+00:00
-- url     : https://prove2.me/submissions/b741420a-7a42-48f1-a6fc-6a6c84eccd2b

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
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_shift_comm_phase_of_pairing_zero

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FiniteFieldPauli
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.FiniteFieldPauli
theorem _root_.solution
    {κ₀ κ₂ : Type v} [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (x z : Word F ι)
    (hx : x ∈ K.firstCoboundaryCheckCode.carrier)
    (hz : z ∈ K.middleBoundaryCode.carrier) :
    shift x * phase z = phase z * shift x := by
  apply shift_comm_phase_of_pairing_zero
  exact (LinearCode.mem_dual K.firstCoboundaryCheckCode z).1
    (K.middleBoundaryCode_le_firstCoboundaryCheckCode_dual hz) x hx
end QEC.Coding.FiniteFieldPauli
