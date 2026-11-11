-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSyndromeWeights.weightedFamily_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:53:59.79714+00:00
-- url     : https://prove2.me/submissions/2f2275cb-de4e-4802-875e-0441e4fbd972

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_weightedFamily_nonneg
import Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_weightedFamily_le_nonzeroFactor
import Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_nonzeroFactor_le_envelope
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
    (A : Finset (Word Bit I)) (t : ℝ) (hA : ∀ x ∈ A, x ≠ 0)
    (M : ℕ) (hM : Fintype.card I ≤ M) :
    0 ≤ weightedFamily A t ∧ weightedFamily A t ≤
      (1 + Real.exp (-t)) ^ M - 1 :=
  ⟨weightedFamily_nonneg A t, (weightedFamily_le_nonzeroFactor A t hA).trans
    (nonzeroFactor_le_envelope I t M hM)⟩
end QEC.Coding.BDL26LocalSyndromeWeights
