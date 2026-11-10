-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDistance.rzQParity_add_owner_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:24:10.439222+00:00
-- url     : https://prove2.me/submissions/4d3abb6c-15ac-44fe-8966-602445fe8cab

import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzQParity_zero_of_other_owner

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDistance
open scoped BigOperators
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26LevelTwoCode
attribute [local instance] QEC.Coding.BDL26LevelTwoDistance.rzQDecidableEq
open BDL26DecodingGraph
namespace QEC.Coding.BDL26LevelTwoDistance
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (first second : Word Field (RZQ P S)) (a b : Vertex P)
    (ha : ∀ c, first c ≠ 0 → BDL26ReplacementSupport.rzCorrectionOwner P S c = a)
    (hb : ∀ c, second c ≠ 0 → BDL26ReplacementSupport.rzCorrectionOwner P S c = b)
    (q : P.Q) (hq : rzQParity P S (first + second) q ≠ 0) :
    Vertex.q q = a ∨ Vertex.q q = b := by
  by_contra hn
  push Not at hn
  have hf := rzQParity_zero_of_other_owner P S first a ha q hn.1
  have hs := rzQParity_zero_of_other_owner P S second b hb q hn.2
  have heq := congrFun ((rzQParity P S).map_add first second) q
  rw [Pi.add_apply, hf, hs, zero_add] at heq
  exact hq heq
end QEC.Coding.BDL26LevelTwoDistance
