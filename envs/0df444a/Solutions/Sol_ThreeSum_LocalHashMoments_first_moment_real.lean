-- Prove2me | solution 1 for ThreeSum.LocalHashMoments.first_moment_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:33.662309+00:00
-- url     : https://prove2.me/submissions/ce7b4231-e9d5-4e8f-bd5b-9264b7625e50

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_Greedy
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Theorems.Thm_ThreeSum_LocalHashMoments_first_moment
import Theorems.Thm_ThreeSum_LocalGraph_edge_card


set_option autoImplicit false
open ThreeSum ThreeSum.LocalHashMoments
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {L h : ℕ}
namespace ThreeSum.LocalHashMoments
theorem _root_.solution (hsep : 2 * h < L) (target : K × K) :
    mean L h (Fintype.card K) * Fintype.card (Weight L K) / 2 ≤
      ∑ w, (hitCount L h (bucketBound L h (Fintype.card K)) w target : ℝ) := by
  have hm := first_moment (K := K) hsep target
  have hp : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have he : (Fintype.card (Edge L h) : ℝ) =
      (outputCount L h : ℝ) * groupSize h := by
    exact_mod_cast edge_card L h
  have hmR : (Fintype.card (Edge L h) : ℝ) * Fintype.card (Weight L K) ≤
      2 * (Fintype.card K : ℝ) ^ 2 *
        ∑ w, (hitCount L h (bucketBound L h (Fintype.card K)) w target : ℝ) := by
    exact_mod_cast hm
  rw [he] at hmR
  unfold mean
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (pow_pos hp 2)).mpr
  nlinarith
end ThreeSum.LocalHashMoments
