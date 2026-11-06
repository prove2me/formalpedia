-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.generatorRank_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:11:13.942489+00:00
-- url     : https://prove2.me/submissions/ba909f4a-4ce3-4cde-9d49-c6c1e61abcdb

import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_Parameters
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_generatedVectorSubspace_eq_span_generators

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
universe u v
open QEC.Coding.StabilizerCode
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.generatorRank = Fintype.card κ := by
  rw [generatorRank, P.generatedVectorSubspace_eq_span_generators]
  exact finrank_span_eq_card P.independent
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
