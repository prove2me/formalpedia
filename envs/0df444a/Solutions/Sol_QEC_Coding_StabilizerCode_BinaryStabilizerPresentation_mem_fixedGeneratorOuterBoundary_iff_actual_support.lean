-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_fixedGeneratorOuterBoundary_iff_actual_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:11:35.894315+00:00
-- url     : https://prove2.me/submissions/f5fbefdf-f304-4888-83db-768f7c5a5ecc

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
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A : Set ι) (q : ι) :
    q ∈ P.fixedGeneratorOuterBoundary A ↔
      q ∉ A ∧ ∃ p : ι, p ∈ A ∧ p ≠ q ∧ ∃ j : κ,
        p ∈ support (P.generators j) ∧ q ∈ support (P.generators j) := by
  constructor
  · rintro ⟨hqA, p, hpA, hpq⟩
    rcases (P.fixedGeneratorInteractionGraph_adj_iff_actual_support p q).1 hpq with
      ⟨hpq, j, hpj, hqj⟩
    exact ⟨hqA, p, hpA, hpq, j, hpj, hqj⟩
  · rintro ⟨hqA, p, hpA, hpq, j, hpj, hqj⟩
    exact ⟨hqA, p, hpA,
      (P.fixedGeneratorInteractionGraph_adj_iff_actual_support p q).2
        ⟨hpq, j, hpj, hqj⟩⟩
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
