-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSyndromeWeights.rxWeightFactor_eq_original_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:56:46.149203+00:00
-- url     : https://prove2.me/submissions/3ee86cf3-e935-40d0-8f14-65c5cf656170

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_fiberExtend_injective

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalSyndromeWeights
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26ReplacementSupport BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26FiniteAlternatingCore BDL26DecodingGraph BDL26BoundedValence
open scoped BigOperators Classical
namespace QEC.Coding.BDL26LocalSyndromeWeights
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (u : Vertex P) (A : Finset (Word Bit (RXFiber P S u))) (t : ℝ) :
    rxWeightFactor P S u A t =
      weightedFamily (A.image (fiberExtend (rxSyndromeOwner P S) u)) t := by
  classical
  unfold rxWeightFactor fiberFactor weightedFamily
  rw [Finset.sum_image]
  intro x _ y _ hxy
  exact fiberExtend_injective (rxSyndromeOwner P S) u hxy
end QEC.Coding.BDL26LocalSyndromeWeights
