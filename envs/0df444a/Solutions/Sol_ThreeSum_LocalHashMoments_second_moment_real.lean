-- Prove2me | solution 1 for ThreeSum.LocalHashMoments.second_moment_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:41:11.334192+00:00
-- url     : https://prove2.me/submissions/8d6c7806-a987-495c-a47d-a5e9d7710d79

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_Greedy
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Theorems.Thm_ThreeSum_LocalHashMoments_second_moment
import Theorems.Thm_ThreeSum_LocalGraph_edge_card


set_option autoImplicit false
open ThreeSum ThreeSum.LocalHashMoments
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {L h : ℕ}
namespace ThreeSum.LocalHashMoments
theorem _root_.solution (hsep : 2 * h < L)
    (hDelta : degree L h ≤ Fintype.card K)
    (hG : groupSize h ≤ Fintype.card K)
    (hE : outputCount L h * groupSize h ≤ Fintype.card K ^ 2)
    (target : K × K) (B : ℕ) :
    (∑ w, (hitCount L h B w target : ℝ) ^ 2) ≤
      5 * mean L h (Fintype.card K) * Fintype.card (Weight L K) := by
  have hm := second_moment (K := K) hsep hDelta hG hE target B
  have hp : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hmR : (Fintype.card K : ℝ) ^ 2 *
        (∑ w, (hitCount L h B w target : ℝ) ^ 2) ≤
      5 * (Fintype.card (Edge L h) : ℝ) * Fintype.card (Weight L K) := by
    exact_mod_cast hm
  have he : (Fintype.card (Edge L h) : ℝ) =
      (outputCount L h : ℝ) * groupSize h := by
    exact_mod_cast edge_card L h
  rw [he] at hmR
  calc
    _ ≤ (5 * ((outputCount L h : ℝ) * groupSize h) *
        Fintype.card (Weight L K)) / (Fintype.card K : ℝ) ^ 2 := by
      apply (le_div_iff₀ (pow_pos hp 2)).mpr
      nlinarith
    _ = _ := by unfold mean; ring
end ThreeSum.LocalHashMoments
