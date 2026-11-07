-- Prove2me | solution 1 for QEC.Coding.FiniteFieldPauli.pauli_eq_self_of_checks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:52:40.016241+00:00
-- url     : https://prove2.me/submissions/2cae81c4-77f4-4fd0-bedc-29c16cb32a19

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
    (x z : Word F ι)
    (hx : x ∈ xCode.carrier) (hz : z ∈ zCode.carrier)
    (ψ : Register F ι) (hψ : ψ ∈ (cssQuantumCode xCode zCode).carrier) :
    pauli x z ψ = ψ := by
  obtain ⟨hX, hZ⟩ := (mem_cssQuantumCode_iff xCode zCode ψ).1 hψ
  rw [pauli, Module.End.mul_apply, hZ z hz, hX x hx]
end QEC.Coding.FiniteFieldPauli
