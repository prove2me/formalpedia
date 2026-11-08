-- Prove2me | solution 1 for QEC.Coding.FiniteFieldPauli.mem_chainComplex_cssQuantumCode_iff_elementaryChecks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:26:13.340026+00:00
-- url     : https://prove2.me/submissions/d50aaed5-ce6b-4a48-90b1-ddfb4bbe85e3

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
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_shift_linearMap_fixed_of_canonicalBasis
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_phase_linearMap_fixed_of_canonicalBasis

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
    (ψ : Register F ι) :
    ψ ∈ (cssQuantumCode
      K.firstCoboundaryCheckCode K.middleBoundaryCode).carrier ↔
      (∀ (k : κ₀) (a : F),
        shift (wordLinearMapTranspose K.boundary1
          (a • canonicalBasisWord k)) ψ = ψ) ∧
      (∀ (k : κ₂) (a : F),
        phase (K.boundary2 (a • canonicalBasisWord k)) ψ = ψ) := by
  constructor
  · intro hψ
    obtain ⟨hX, hZ⟩ := (mem_cssQuantumCode_iff
      K.firstCoboundaryCheckCode K.middleBoundaryCode ψ).1 hψ
    constructor
    · intro k a
      apply hX
      exact (K.mem_firstCoboundaryCheckCode_iff _).2
        ⟨a • canonicalBasisWord k, rfl⟩
    · intro k a
      apply hZ
      exact (K.mem_middleBoundaryCode_iff _).2
        ⟨a • canonicalBasisWord k, rfl⟩
  · rintro ⟨hX, hZ⟩
    apply (mem_cssQuantumCode_iff
      K.firstCoboundaryCheckCode K.middleBoundaryCode ψ).2
    constructor
    · intro x hx
      obtain ⟨y, rfl⟩ := (K.mem_firstCoboundaryCheckCode_iff x).1 hx
      exact shift_linearMap_fixed_of_canonicalBasis
        (wordLinearMapTranspose K.boundary1) ψ hX y
    · intro z hz
      obtain ⟨y, rfl⟩ := (K.mem_middleBoundaryCode_iff z).1 hz
      exact phase_linearMap_fixed_of_canonicalBasis K.boundary2 ψ hZ y
end QEC.Coding.FiniteFieldPauli
