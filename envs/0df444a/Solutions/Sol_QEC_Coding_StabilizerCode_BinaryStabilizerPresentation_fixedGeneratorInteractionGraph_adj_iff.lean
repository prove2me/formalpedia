-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorInteractionGraph_adj_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:11:35.111226+00:00
-- url     : https://prove2.me/submissions/f2ddd1b2-80ef-4fff-84f1-e6680e667843

import Definitions.Def_QEC_Coding_Stabilizer_Parameters
import Definitions.Def_QEC_Locality_Graph_Core
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction

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
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (p q : ι) :
    P.fixedGeneratorInteractionGraph.adjacent p q ↔
      p ≠ q ∧ ∃ j : κ, p ∈ P.generatorSupport j ∧ q ∈ P.generatorSupport j :=
  Iff.rfl
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
