-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.weight_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:18:26.280011+00:00
-- url     : https://prove2.me/submissions/c90675eb-ff02-4609-962d-c20c755cebf2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_active_count_le_weight
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_lower_weight_le_neighbors
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_neighbors_card_le_sharp
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_sharp_le_seven_activeX
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_seven_activeX_le_seven_count

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXActiveErrorTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open BDL26BoundedValence BDL26GraphQuantitativeBounds
open scoped BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXActiveErrorTransport
theorem _root_.solution (a b : Upper S depth i) :
    HammingWeight (L S depth i h a b) ≤ (N S depth i h a b).card ∧
      (N S depth i h a b).card ≤ (activeQ S depth i h (a+b)).card+
        ∑ x ∈ activeX S depth i h (a+b), (incidentQ S depth i x).card ∧
      (activeQ S depth i h (a+b)).card+∑ x ∈ activeX S depth i h (a+b), (incidentQ S depth i x).card ≤
        (activeQ S depth i h (a+b)).card+7*(activeX S depth i h (a+b)).card ∧
      (activeQ S depth i h (a+b)).card+7*(activeX S depth i h (a+b)).card ≤
        7*((activeX S depth i h (a+b)).card+(activeQ S depth i h (a+b)).card) ∧
      7*((activeX S depth i h (a+b)).card+(activeQ S depth i h (a+b)).card) ≤ 7*HammingWeight (a+b) :=
  ⟨lower_weight_le_neighbors S depth i h a b,neighbors_card_le_sharp S depth i h a b,
    sharp_le_seven_activeX S depth i h a b,seven_activeX_le_seven_count S depth i h a b,
    Nat.mul_le_mul_left 7 (active_count_le_weight S depth i h (a+b))⟩
end QEC.Coding.BDL26RXActiveErrorTransport
