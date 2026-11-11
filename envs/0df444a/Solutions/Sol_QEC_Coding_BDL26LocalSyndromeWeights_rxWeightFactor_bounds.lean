-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSyndromeWeights.rxWeightFactor_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:08:40.740051+00:00
-- url     : https://prove2.me/submissions/c2e2d6c7-e6e5-4ebd-b1f2-d036f7beb060

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_weightedFamily_bounds
import Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_rx_extend_weight
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_rxSyndromeFiber_card_le


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalSyndromeWeights
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26ReplacementSupport BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26FiniteAlternatingCore BDL26DecodingGraph BDL26BoundedValence
open scoped BigOperators Classical
namespace QEC.Coding.BDL26LocalSyndromeWeights
theorem _root_.solution (P : TannerSquarePresentation) (hP : BoundedValence P)
    (S : OddScale) (u : Vertex P) (A : Finset (Word Bit (RXFiber P S u)))
    (t : ℝ) (hA : ∀ x ∈ A, x ≠ 0) :
    0 ≤ rxWeightFactor P S u A t ∧ rxWeightFactor P S u A t ≤
      (1 + Real.exp (-t)) ^ (14 * S.ell^2) - 1 := by
  have heq : rxWeightFactor P S u A t = weightedFamily A t := by
    unfold rxWeightFactor fiberFactor weightedFamily
    apply Finset.sum_congr rfl
    intro x _
    rw [rx_extend_weight]
  rw [heq]
  exact weightedFamily_bounds A t hA (14 * S.ell^2)
    (rxSyndromeFiber_card_le P hP S u)
end QEC.Coding.BDL26LocalSyndromeWeights
