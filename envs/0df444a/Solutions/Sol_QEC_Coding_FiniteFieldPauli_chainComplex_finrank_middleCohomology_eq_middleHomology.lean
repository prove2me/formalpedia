-- Prove2me | solution 1 for QEC.Coding.FiniteFieldPauli.chainComplex_finrank_middleCohomology_eq_middleHomology
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:54:55.482899+00:00
-- url     : https://prove2.me/submissions/edda42df-4a76-4524-9682-246e5c8339d2

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
import Theorems.Thm_QEC_Coding_LinearCode_dimension_add_dual_dimension_eq_length


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
    Module.finrank F K.middleCohomology = Module.finrank F K.middleHomology := by
  have hcoh := Submodule.finrank_quotient_add_finrank K.middleCoboundaryInCocycles
  have hcob : Module.finrank F K.middleCoboundaryInCocycles =
      Dimension K.firstCoboundaryCheckCode := by
    rw [Dimension_eq_finrank_carrier]
    exact K.middleCoboundaryInCocyclesEquiv.finrank_eq
  have hcohSum : Module.finrank F K.middleCohomology +
      Dimension K.firstCoboundaryCheckCode =
      Dimension K.middleCocycleCode := by
    rw [← hcob, Dimension_eq_finrank_carrier]
    exact hcoh
  have hhom := Submodule.finrank_quotient_add_finrank K.middleBoundaryInCycles
  have hbound : Module.finrank F K.middleBoundaryInCycles =
      Dimension K.middleBoundaryCode := K.finrank_middleBoundaryInCycles_eq
  have hhomSum : Module.finrank F K.middleHomology +
      Dimension K.middleBoundaryCode = Dimension K.middleCycleCode := by
    rw [← hbound, Dimension_eq_finrank_carrier]
    exact hhom
  have hdualZ : Dimension K.middleCocycleCode +
      Dimension K.middleBoundaryCode = Length F ι := by
    have h := K.middleBoundaryCode.dimension_add_dual_dimension_eq_length
    have heq : Dimension K.middleBoundaryCode.dual =
        Dimension K.middleCocycleCode := by
      rw [Dimension_eq_finrank_carrier, Dimension_eq_finrank_carrier,
        K.middleBoundaryCode_dual_carrier_eq_middleCocycleCode]
    omega
  have hdualX : Dimension K.middleCycleCode +
      Dimension K.firstCoboundaryCheckCode = Length F ι := by
    have h := K.firstCoboundaryCheckCode.dimension_add_dual_dimension_eq_length
    have heq : Dimension K.firstCoboundaryCheckCode.dual =
        Dimension K.middleCycleCode := by
      rw [Dimension_eq_finrank_carrier, Dimension_eq_finrank_carrier,
        K.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode]
    omega
  omega
end QEC.Coding.FiniteFieldPauli
