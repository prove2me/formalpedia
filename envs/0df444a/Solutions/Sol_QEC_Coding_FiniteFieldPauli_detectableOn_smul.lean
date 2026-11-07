-- Prove2me | solution 1 for QEC.Coding.FiniteFieldPauli.detectableOn_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:52:09.071207+00:00
-- url     : https://prove2.me/submissions/192c9621-ccd6-4245-a021-e4c8113c224c

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
theorem _root_.solution
    (C : Semantics.QuantumCode (Register F ι))
    (E : Semantics.Operator (Register F ι)) (a : Complex)
    (hE : Semantics.DetectableOn C E) :
    Semantics.DetectableOn C (a • E) := by
  obtain ⟨c, hc⟩ := hE
  refine ⟨a * c, ?_⟩
  intro u hu v hv
  change inner Complex u (a • E v) = (a * c) * inner Complex u v
  rw [inner_smul_right, hc u hu v hv]
  ring
end QEC.Coding.FiniteFieldPauli
