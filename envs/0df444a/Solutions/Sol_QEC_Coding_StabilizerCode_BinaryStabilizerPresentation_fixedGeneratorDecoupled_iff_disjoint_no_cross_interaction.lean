-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorDecoupled_iff_disjoint_no_cross_interaction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:11:57.336397+00:00
-- url     : https://prove2.me/submissions/dad17812-5054-437b-b72e-0b3d10348a4c

import Definitions.Def_QEC_Coding_Stabilizer_Parameters
import Definitions.Def_QEC_Locality_Graph_Core
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_fixedGeneratorNoCrossEdge_iff_no_cross_interaction

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
    P.fixedGeneratorDecoupled A B ↔
      Disjoint A B ∧ ∀ ⦃p : ι⦄, p ∈ A → ∀ ⦃q : ι⦄, q ∈ B →
        ∀ j : κ,
          ¬ (p ∈ support (P.generators j) ∧ q ∈ support (P.generators j)) := by
  constructor
  · rintro ⟨hdisjoint, hnoedge⟩
    refine ⟨hdisjoint, ?_⟩
    have hsupport :=
      (P.fixedGeneratorNoCrossEdge_iff_no_cross_interaction A B).1 hnoedge
    intro p hp q hq j hpq
    have hne : p ≠ q := by
      intro hpq
      subst q
      exact (Set.disjoint_left.1 hdisjoint) hp hq
    exact hsupport hp hq hne j hpq
  · rintro ⟨hdisjoint, hsupport⟩
    refine ⟨hdisjoint, ?_⟩
    refine (P.fixedGeneratorNoCrossEdge_iff_no_cross_interaction A B).2 ?_
    intro p hp q hq _hne j hpq
    exact hsupport hp hq j hpq
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
