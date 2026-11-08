-- Prove2me | solution 1 for QEC.Coding.FiniteFieldPauli.pauliSupport_card_ge_of_not_detectable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:02:48.797849+00:00
-- url     : https://prove2.me/submissions/a847cde9-c004-4f66-b5d4-a4c99be5b2fc

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
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_detectable_pauli_iff
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_hammingWeight_x_le_pauliSupport
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_hammingWeight_z_le_pauliSupport

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FiniteFieldPauli
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.FiniteFieldPauli
theorem _root_.solution
    [DecidableEq F] (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (d : Nat) (hminimum : AlgebraicCSSMinimumDistance xCode zCode d)
    (x z : Word F ι)
    (hnot : ¬ Semantics.DetectableOn (cssQuantumCode xCode zCode) (pauli x z)) :
    d ≤ (pauliSupport x z).card := by
  have hx : x ∈ zCode.dual.carrier := by
    by_contra h
    exact hnot ((detectable_pauli_iff xCode zCode horth x z).2 (Or.inl h))
  have hz : z ∈ xCode.dual.carrier := by
    by_contra h
    exact hnot ((detectable_pauli_iff xCode zCode horth x z).2
      (Or.inr (Or.inl h)))
  have hlogical : x ∉ xCode.carrier ∨ z ∉ zCode.carrier := by
    by_contra h
    push Not at h
    exact hnot ((detectable_pauli_iff xCode zCode horth x z).2
      (Or.inr (Or.inr h)))
  obtain ⟨_, _, _, hleast⟩ := hminimum
  rcases hlogical with hxnot | hznot
  · exact (hleast x (Or.inl ⟨hx, hxnot⟩)).trans
      (hammingWeight_x_le_pauliSupport x z)
  · exact (hleast z (Or.inr ⟨hz, hznot⟩)).trans
      (hammingWeight_z_le_pauliSupport x z)
end QEC.Coding.FiniteFieldPauli
