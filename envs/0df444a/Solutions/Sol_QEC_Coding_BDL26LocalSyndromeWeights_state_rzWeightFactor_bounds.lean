-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSyndromeWeights.state_rzWeightFactor_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:25:17.796219+00:00
-- url     : https://prove2.me/submissions/db166fc5-e1fc-4ceb-9534-e4a1deabfe9d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_rzWeightFactor_bounds
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
theorem _root_.solution (S : OddScale) (n : ℕ) (z : (state S n).presentation.Z)
    (A : Finset (Word Bit (RZFiber (state S n).presentation S z)))
    (t : ℝ) (hA : ∀ x ∈ A, x ≠ 0) :
    0 ≤ rzWeightFactor (state S n).presentation S z A t ∧
      rzWeightFactor (state S n).presentation S z A t ≤
        (1 + Real.exp (-t)) ^ (14 * S.ell^2) - 1 :=
  rzWeightFactor_bounds _ (state S n).admissible.toTannerSquareAdmissible
    (state_boundedValence S n) S z A t hA
end QEC.Coding.BDL26LocalSyndromeWeights
