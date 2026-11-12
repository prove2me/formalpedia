-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSyndromeWeights.state_rx_source_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:56:53.274274+00:00
-- url     : https://prove2.me/submissions/2b1964fd-fe64-438f-b993-47a83cd40d86

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_state_rxWeightFactor_bounds

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalSyndromeWeights
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26ReplacementSupport BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26FiniteAlternatingCore BDL26DecodingGraph BDL26BoundedValence
open scoped BigOperators Classical
namespace QEC.Coding.BDL26LocalSyndromeWeights
theorem _root_.solution (S : OddScale) (n : ℕ)
    (u : Vertex (state S n).presentation)
    (A : Finset (Word Bit (RXFiber (state S n).presentation S u)))
    (beta : ℝ) (hA : ∀ x ∈ A, x ≠ 0) :
    0 ≤ rxWeightFactor (state S n).presentation S u A (beta/4) ∧
      rxWeightFactor (state S n).presentation S u A (beta/4) ≤ sourceEnvelope S beta :=
  state_rxWeightFactor_bounds S n u A (beta/4) hA
end QEC.Coding.BDL26LocalSyndromeWeights
