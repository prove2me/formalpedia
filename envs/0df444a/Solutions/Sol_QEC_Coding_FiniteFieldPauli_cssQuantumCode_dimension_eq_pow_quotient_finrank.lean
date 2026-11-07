-- Prove2me | solution 1 for QEC.Coding.FiniteFieldPauli.cssQuantumCode_dimension_eq_pow_quotient_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:56:39.059512+00:00
-- url     : https://prove2.me/submissions/2ea5e262-040a-46b5-96af-d06683954d04

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
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_cssQuantumCode_dimension_eq_card_cosets

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FiniteFieldPauli
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.FiniteFieldPauli
theorem _root_.solution
    (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier) :
    (cssQuantumCode xCode zCode).dimension =
      (Fintype.card F) ^
        Module.finrank F (zCode.dual.carrier ⧸ xWithinDual xCode zCode) := by
  rw [cssQuantumCode_dimension_eq_card_cosets xCode zCode horth]
  rw [← Fintype.card_congr (admissibleCosetEquivDualQuotient xCode zCode horth)]
  exact Module.card_eq_pow_finrank
end QEC.Coding.FiniteFieldPauli
