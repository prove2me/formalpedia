-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorNoCrossEdge_iff_no_cross_interaction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:45:24.993949+00:00
-- url     : https://prove2.me/submissions/5164e5ce-2db1-4d15-8d5c-04277dac1ad4

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
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A B : Set ι) :
    P.fixedGeneratorNoCrossEdge A B ↔
      ∀ ⦃p : ι⦄, p ∈ A → ∀ ⦃q : ι⦄, q ∈ B → p ≠ q →
        ∀ j : κ,
          ¬ (p ∈ support (P.generators j) ∧ q ∈ support (P.generators j)) := by
  constructor
  · intro h p hp q hq hpq j hsupport
    exact h hp hq
      ((P.fixedGeneratorInteractionGraph_adj_iff_actual_support p q).2
        ⟨hpq, j, hsupport.1, hsupport.2⟩)
  · intro h p hp q hq hpq
    rcases (P.fixedGeneratorInteractionGraph_adj_iff_actual_support p q).1 hpq with
      ⟨hpq, j, hpj, hqj⟩
    exact h hp hq hpq j ⟨hpj, hqj⟩
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
