-- Prove2me | solution 1 for QEC.Coding.FiniteFieldPauli.detectableOn_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:52:12.145071+00:00
-- url     : https://prove2.me/submissions/54bc514f-96ac-420e-a1f7-e583cac70c29

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
    (E G : Semantics.Operator (Register F ι))
    (hE : Semantics.DetectableOn C E)
    (hG : Semantics.DetectableOn C G) :
    Semantics.DetectableOn C (E + G) := by
  obtain ⟨a, ha⟩ := hE
  obtain ⟨b, hb⟩ := hG
  refine ⟨a + b, ?_⟩
  intro u hu v hv
  change inner Complex u (E v + G v) = (a + b) * inner Complex u v
  rw [inner_add_right, ha u hu v hv, hb u hu v hv]
  ring
end QEC.Coding.FiniteFieldPauli
