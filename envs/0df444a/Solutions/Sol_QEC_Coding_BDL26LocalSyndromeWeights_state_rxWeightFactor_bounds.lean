-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSyndromeWeights.state_rxWeightFactor_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:22:42.393005+00:00
-- url     : https://prove2.me/submissions/5ff3bf0f-b71e-4246-8f78-32f40be2a5ee

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_rxWeightFactor_bounds
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence


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
    (t : ℝ) (hA : ∀ x ∈ A, x ≠ 0) :
    0 ≤ rxWeightFactor (state S n).presentation S u A t ∧
      rxWeightFactor (state S n).presentation S u A t ≤
        (1 + Real.exp (-t)) ^ (14 * S.ell^2) - 1 :=
  rxWeightFactor_bounds _ (state_boundedValence S n) S u A t hA
end QEC.Coding.BDL26LocalSyndromeWeights
