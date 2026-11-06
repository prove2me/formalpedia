-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.isFixedGeneratorTwoThirdsBalancedVertexSeparator_iff_actual_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:12:28.63901+00:00
-- url     : https://prove2.me/submissions/c7bfd526-8eb5-4002-acee-3c87a2058c39

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_fixedGeneratorNoEdgeBetween_iff_actual_support

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (vertices separator : Finset ι) :
    P.IsFixedGeneratorTwoThirdsBalancedVertexSeparator vertices separator ↔
      ∃ left right : Finset ι,
        separator ⊆ vertices ∧
          left ∪ right = vertices \ separator ∧
          Disjoint left right ∧
          3 * left.card ≤ 2 * vertices.card ∧
          3 * right.card ≤ 2 * vertices.card ∧
          ∀ ⦃p : ι⦄, p ∈ left → ∀ ⦃q : ι⦄, q ∈ right →
            ¬ (p ≠ q ∧ ∃ j : κ,
              p ∈ support (P.generators j) ∧ q ∈ support (P.generators j)) := by
  constructor
  · rintro ⟨left, right, hseparator, hpartition, hdisjoint, hleft, hright, hnoedge⟩
    exact ⟨left, right, hseparator, hpartition, hdisjoint, hleft, hright,
      (P.fixedGeneratorNoEdgeBetween_iff_actual_support left right).1 hnoedge⟩
  · rintro ⟨left, right, hseparator, hpartition, hdisjoint, hleft, hright, hnoedge⟩
    exact ⟨left, right, hseparator, hpartition, hdisjoint, hleft, hright,
      (P.fixedGeneratorNoEdgeBetween_iff_actual_support left right).2 hnoedge⟩
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
