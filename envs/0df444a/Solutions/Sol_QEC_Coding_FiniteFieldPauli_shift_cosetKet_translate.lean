-- Prove2me | solution 1 for QEC.Coding.FiniteFieldPauli.shift_cosetKet_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:51:26.715711+00:00
-- url     : https://prove2.me/submissions/14e69ec5-ec9b-4b66-a03c-b24bf60fed83

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
theorem _root_.solution (xCode : LinearCode F ι)
    (a x : Word F ι) :
    shift x (cosetKet xCode a) = cosetKet xCode (a - x) := by
  classical
  ext η
  rw [shift_apply, cosetKet_apply, cosetKet_apply]
  have hrewrite : η + x - a = η - (a - x) := by abel
  rw [hrewrite]
end QEC.Coding.FiniteFieldPauli
