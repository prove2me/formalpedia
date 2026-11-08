-- Prove2me | solution 1 for QEC.Coding.FiniteFieldPauli.chainComplex_cssQuantumCode_dimension_eq_pow_cohomology
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:58:32.407204+00:00
-- url     : https://prove2.me/submissions/619cb144-4b98-4fc9-9bdb-934e5753edf2

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
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_cssQuantumCode_dimension_eq_pow_quotient_finrank

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FiniteFieldPauli
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.FiniteFieldPauli
theorem _root_.solution
    {κ₀ κ₂ : Type v} [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂)) :
    (cssQuantumCode K.firstCoboundaryCheckCode K.middleBoundaryCode).dimension =
      (Fintype.card F) ^ Module.finrank F K.middleCohomology := by
  rw [cssQuantumCode_dimension_eq_pow_quotient_finrank
    K.firstCoboundaryCheckCode K.middleBoundaryCode
    K.firstCoboundaryCheckCode_le_middleBoundaryCode_dual]
  exact congrArg ((Fintype.card F) ^ ·)
    K.pureXLogicalQuotientEquivMiddleCohomology.finrank_eq
end QEC.Coding.FiniteFieldPauli
