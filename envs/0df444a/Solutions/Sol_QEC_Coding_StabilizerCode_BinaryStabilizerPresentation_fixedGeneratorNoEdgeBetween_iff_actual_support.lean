-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorNoEdgeBetween_iff_actual_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:07:20.523012+00:00
-- url     : https://prove2.me/submissions/164396e2-1a3b-4ead-8576-6c52d27dd98c

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_fixedGeneratorInteractionGraph_adj_iff_actual_support


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (left right : Finset ι) :
    P.fixedGeneratorNoEdgeBetween left right ↔
      ∀ ⦃p : ι⦄, p ∈ left → ∀ ⦃q : ι⦄, q ∈ right →
        ¬ (p ≠ q ∧ ∃ j : κ,
          p ∈ support (P.generators j) ∧ q ∈ support (P.generators j)) := by
  constructor
  · intro h p hp q hq hsupport
    apply h hp hq
    exact (P.fixedGeneratorInteractionGraph_adj_iff_actual_support p q).2 hsupport
  · intro h p hp q hq hadjacent
    exact h hp hq
      ((P.fixedGeneratorInteractionGraph_adj_iff_actual_support p q).1 hadjacent)
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
