-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSyndromeWeights.fiberFactor_eq_weightedFamily
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:02:32.273586+00:00
-- url     : https://prove2.me/submissions/f5936646-45a9-477c-a3fb-277c910a008d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_fiberExtend_weight

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalSyndromeWeights
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26ReplacementSupport BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26FiniteAlternatingCore BDL26DecodingGraph BDL26BoundedValence
open scoped BigOperators Classical
namespace QEC.Coding.BDL26LocalSyndromeWeights
theorem _root_.solution {C Label : Type*} [Fintype C]
    (owner : C → Label) (label : Label)
    (A : Finset (Word Bit {c : C // owner c = label})) (t : ℝ) :
    fiberFactor owner label A t = weightedFamily A t := by
  unfold fiberFactor weightedFamily
  apply Finset.sum_congr rfl
  intro x _
  rw [fiberExtend_weight]
end QEC.Coding.BDL26LocalSyndromeWeights
