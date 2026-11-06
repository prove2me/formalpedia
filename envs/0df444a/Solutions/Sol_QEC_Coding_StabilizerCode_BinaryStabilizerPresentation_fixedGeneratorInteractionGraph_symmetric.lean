-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorInteractionGraph_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:29:47.550272+00:00
-- url     : https://prove2.me/submissions/d678281d-3380-46a1-800a-6bd5aa0eccce

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
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) {p q : ι}
    (h : P.fixedGeneratorInteractionGraph.adjacent p q) :
    P.fixedGeneratorInteractionGraph.adjacent q p :=
  P.fixedGeneratorInteractionGraph.symmetric h
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
