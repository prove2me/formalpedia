-- Prove2me | solution 1 for QEC.Coding.BDL26RXCoarseInfluence.basisSyndrome_zero_on_readRegion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:19:41.529094+00:00
-- url     : https://prove2.me/submissions/adcc323d-31c5-4179-a198-25c41c7af797

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_mem_influence

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXCoarseInfluence
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXCoarseInfluence
theorem _root_.solution (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (q : FamilyQ S depth i.succ) (z : FamilyZ S depth i.castSucc)
    (hz : z ∉ influence S depth i h q) (p : FamilyZ S depth i.succ)
    (hp : p ∈ readRegion S depth i h z) : basisSyndrome S depth i q p = 0 := by
  by_contra hp0
  exact hz ((mem_influence S depth i h q z).mpr ⟨p, hp0, hp⟩)
end QEC.Coding.BDL26RXCoarseInfluence
