-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_fixedGeneratorInnerBoundary_iff_actual_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:11:46.808862+00:00
-- url     : https://prove2.me/submissions/11121493-4517-49c5-a84f-22d56bad3a70

import Definitions.Def_QEC_Coding_Stabilizer_Parameters
import Definitions.Def_QEC_Locality_Graph_Core
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_fixedGeneratorInteractionGraph_adj_iff_actual_support

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A : Set ι) (p : ι) :
    p ∈ P.fixedGeneratorInnerBoundary A ↔
      p ∈ A ∧ ∃ q : ι, q ∉ A ∧ p ≠ q ∧ ∃ j : κ,
        p ∈ support (P.generators j) ∧ q ∈ support (P.generators j) := by
  constructor
  · rintro ⟨hpA, q, hqA, hpq⟩
    rcases (P.fixedGeneratorInteractionGraph_adj_iff_actual_support p q).1 hpq with
      ⟨hpq, j, hpj, hqj⟩
    exact ⟨hpA, q, hqA, hpq, j, hpj, hqj⟩
  · rintro ⟨hpA, q, hqA, hpq, j, hpj, hqj⟩
    exact ⟨hpA, q, hqA,
      (P.fixedGeneratorInteractionGraph_adj_iff_actual_support p q).2
        ⟨hpq, j, hpj, hqj⟩⟩
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
