-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSyndromeWeights.rzWeightFactor_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:21:27.34849+00:00
-- url     : https://prove2.me/submissions/105800c9-1447-456b-8714-4d3ee5a46cbc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_weightedFamily_bounds
import Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_rz_extend_weight
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_rzSyndromeFiber_card_le


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalSyndromeWeights
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26ReplacementSupport BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26FiniteAlternatingCore BDL26DecodingGraph BDL26BoundedValence
open scoped BigOperators Classical
namespace QEC.Coding.BDL26LocalSyndromeWeights
theorem _root_.solution (P : TannerSquarePresentation) (aP : TannerSquareAdmissible P)
    (hP : BoundedValence P) (S : OddScale) (z : P.Z)
    (A : Finset (Word Bit (RZFiber P S z))) (t : ℝ) (hA : ∀ x ∈ A, x ≠ 0) :
    0 ≤ rzWeightFactor P S z A t ∧ rzWeightFactor P S z A t ≤
      (1 + Real.exp (-t)) ^ (14 * S.ell^2) - 1 := by
  have heq : rzWeightFactor P S z A t = weightedFamily A t := by
    unfold rzWeightFactor fiberFactor weightedFamily
    apply Finset.sum_congr rfl
    intro x _
    rw [rz_extend_weight]
  rw [heq]
  exact weightedFamily_bounds A t hA (14 * S.ell^2)
    (rzSyndromeFiber_card_le P aP hP S z)
end QEC.Coding.BDL26LocalSyndromeWeights
