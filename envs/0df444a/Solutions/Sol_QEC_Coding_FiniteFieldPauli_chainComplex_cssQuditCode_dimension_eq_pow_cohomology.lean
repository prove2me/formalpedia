-- Prove2me | solution 1 for QEC.Coding.FiniteFieldPauli.chainComplex_cssQuditCode_dimension_eq_pow_cohomology
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:01:24.292947+00:00
-- url     : https://prove2.me/submissions/1b1a0c87-8078-44ca-a5b8-bd5704472ebe

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
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_chainComplex_cssQuantumCode_dimension_eq_pow_cohomology
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_cssQuditCode_dimension_eq

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
      (Fintype.card F) ^ Module.finrank F K.middleCohomology := by
  rw [cssQuditCode_dimension_eq]
  exact chainComplex_cssQuantumCode_dimension_eq_pow_cohomology K
end QEC.Coding.FiniteFieldPauli
