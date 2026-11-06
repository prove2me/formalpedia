-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorInducedSubgraph_adj_iff_actual_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:12:08.967326+00:00
-- url     : https://prove2.me/submissions/1cc07dae-d34a-444d-88a8-16548248fb6c

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
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (vertices : Finset ι)
    (p q : {i : ι // i ∈ vertices}) :
    (P.fixedGeneratorInducedSubgraph vertices).adjacent p q ↔
      p.1 ≠ q.1 ∧ ∃ j : κ,
        p.1 ∈ support (P.generators j) ∧ q.1 ∈ support (P.generators j) :=
  P.fixedGeneratorInteractionGraph_adj_iff_actual_support p.1 q.1
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
