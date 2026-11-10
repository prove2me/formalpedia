-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedValence.state_boundedValence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:23:08.3285+00:00
-- url     : https://prove2.me/submissions/a307cfd3-8bb9-47e7-b36b-0858bffbe0c8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_rx_boundedValence
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_rz_boundedValence
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_base_boundedValence
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rx_boundedValence


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26RXLocalReplacement
open BDL26TannerLocalRegularity
namespace QEC.Coding.BDL26BoundedValence
theorem _root_.solution (S : OddScale) (n : Nat) :
    BoundedValence (BDL26DecodingGraph.state S n).presentation := by
  induction n with
  | zero => exact base_boundedValence
  | succ n ih =>
      change BoundedValence (BDL26DecodingGraph.nextState S n
        (BDL26DecodingGraph.state S n)).presentation
      unfold BDL26DecodingGraph.nextState
      split
      · exact rx_boundedValence _ (BDL26DecodingGraph.state S n).admissible
          (BDL26DecodingGraph.state S n).regular S ih
      · exact rz_boundedValence _ (BDL26DecodingGraph.state S n).admissible
          (BDL26DecodingGraph.state S n).regular S ih
end QEC.Coding.BDL26BoundedValence
