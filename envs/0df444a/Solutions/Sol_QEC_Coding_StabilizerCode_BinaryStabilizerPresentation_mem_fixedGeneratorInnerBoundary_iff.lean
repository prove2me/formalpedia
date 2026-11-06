-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_fixedGeneratorInnerBoundary_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:11:46.074959+00:00
-- url     : https://prove2.me/submissions/6368a9b4-0518-456a-8aa7-51ba7f6b5cbc

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
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A : Set ι) (p : ι) :
    p ∈ P.fixedGeneratorInnerBoundary A ↔
      p ∈ A ∧ ∃ q : ι, q ∉ A ∧ P.fixedGeneratorInteractionGraph.adjacent p q :=
  Iff.rfl
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
