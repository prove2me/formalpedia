-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_fixedGeneratorOuterBoundary_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:02:19.687406+00:00
-- url     : https://prove2.me/submissions/6661afa7-113b-47aa-9e81-b82ac28602bb

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
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A : Set ι) (q : ι) :
    q ∈ P.fixedGeneratorOuterBoundary A ↔
      q ∉ A ∧ ∃ p : ι, p ∈ A ∧ P.fixedGeneratorInteractionGraph.adjacent p q :=
  Iff.rfl
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
