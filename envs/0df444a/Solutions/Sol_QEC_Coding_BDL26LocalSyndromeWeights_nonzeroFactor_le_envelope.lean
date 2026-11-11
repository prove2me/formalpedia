-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSyndromeWeights.nonzeroFactor_le_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:48:08.460222+00:00
-- url     : https://prove2.me/submissions/8c1f683f-6041-4c28-8b35-a76c569bc5a6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_nonzeroFactor_eq_power

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalSyndromeWeights
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26ReplacementSupport BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26FiniteAlternatingCore BDL26DecodingGraph BDL26BoundedValence
open scoped BigOperators Classical
namespace QEC.Coding.BDL26LocalSyndromeWeights
theorem _root_.solution (I : Type*) [Fintype I]
    (t : ℝ) (M : ℕ) (hM : Fintype.card I ≤ M) :
    nonzeroFactor I t ≤ (1 + Real.exp (-t)) ^ M - 1 := by
  rw [nonzeroFactor_eq_power]
  exact sub_le_sub_right (pow_le_pow_right₀
    (show 1 ≤ 1 + Real.exp (-t) by linarith [Real.exp_pos (-t)]) hM) 1
end QEC.Coding.BDL26LocalSyndromeWeights
