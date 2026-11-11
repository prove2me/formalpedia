-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSyndromeWeights.weightedFamily_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:46:55.018561+00:00
-- url     : https://prove2.me/submissions/57359be7-254d-4568-a74f-d2bc088d1b49

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalSyndromeWeights
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26ReplacementSupport BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26FiniteAlternatingCore BDL26DecodingGraph BDL26BoundedValence
open scoped BigOperators Classical
namespace QEC.Coding.BDL26LocalSyndromeWeights
theorem _root_.solution {I : Type*} [Fintype I]
    (A : Finset (Word Bit I)) (t : ℝ) : 0 ≤ weightedFamily A t :=
  Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
end QEC.Coding.BDL26LocalSyndromeWeights
