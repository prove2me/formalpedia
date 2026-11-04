-- Prove2me | solution 1 for ThreeSum.LocalHashMoments.cover_has_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:25:28.215207+00:00
-- url     : https://prove2.me/submissions/b3bcd870-732e-4a40-a18b-8d7801327df8

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_Greedy
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_Submission_ThreeSum_LocalHashMoments

set_option autoImplicit false
open ThreeSum ThreeSum.LocalHashMoments
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {L h : ℕ}
namespace ThreeSum.LocalHashMoments
theorem _root_.solution {B : ℕ} {w : Weight L K} {target : K × K}
    (hc : Covers L h B w target) :
    ∃ e : Edge L h, HashFamily.hashValue w (left e) = target.1 ∧
      HashFamily.hashValue w (right e) = target.2 ∧
      HashFamily.bucketSize (leftVertices L h) w target.1 ≤ B ∧
      HashFamily.bucketSize (rightVertices L h) w target.2 ≤ B := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc)
  have ht := (Finset.mem_filter.mp he).2
  have hp := (Finset.mem_filter.mp ht).1
  have hl := (Finset.mem_filter.mp ht).2
  exact ⟨e, (Finset.mem_filter.mp hp).2.1, (Finset.mem_filter.mp hp).2.2, hl⟩
end ThreeSum.LocalHashMoments
