-- Prove2me | solution 1 for QEC.Coding.FiniteFieldPauli.chainComplex_cssQuditCode_dimension_eq_pow_homology
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:26:52.866206+00:00
-- url     : https://prove2.me/submissions/da7d8824-ef06-43df-9033-fb8cfdb010f2

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
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_chainComplex_finrank_middleCohomology_eq_middleHomology
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_chainComplex_cssQuditCode_dimension_eq_pow_cohomology

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FiniteFieldPauli
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.FiniteFieldPauli
theorem _root_.solution
    {ι' κ₀ κ₂ : Type u} [Fintype ι'] [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι') (Word F κ₂)) :
    (cssQuditCode K.firstCoboundaryCheckCode K.middleBoundaryCode).dimension =
      (Fintype.card F) ^ Module.finrank F K.middleHomology := by
  rw [chainComplex_cssQuditCode_dimension_eq_pow_cohomology K,
    chainComplex_finrank_middleCohomology_eq_middleHomology K]
end QEC.Coding.FiniteFieldPauli
