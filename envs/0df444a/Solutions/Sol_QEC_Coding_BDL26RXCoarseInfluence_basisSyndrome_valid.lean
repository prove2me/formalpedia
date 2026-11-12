-- Prove2me | solution 1 for QEC.Coding.BDL26RXCoarseInfluence.basisSyndrome_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:09:55.266099+00:00
-- url     : https://prove2.me/submissions/5ae1ae50-1cd9-4937-a752-080227fdb611

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXCoarseInfluence
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXCoarseInfluence
theorem _root_.solution (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (q : FamilyQ S depth i.succ) :
    basisSyndrome S depth i q ∈ (indexedFamily S depth).syndromeSubmodule i.succ :=
  ⟨canonicalBasisWord q, rfl⟩
end QEC.Coding.BDL26RXCoarseInfluence
