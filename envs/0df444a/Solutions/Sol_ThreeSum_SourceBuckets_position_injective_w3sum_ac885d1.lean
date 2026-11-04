-- Prove2me | solution 1 for ThreeSum.SourceBuckets.position_injective_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:18:54.869448+00:00
-- url     : https://prove2.me/submissions/7b217bd1-3964-4d09-ab97-f338964b1bad

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Theorems.Thm_ThreeSum_SourceBuckets_count_strict
import Theorems.Thm_ThreeSum_SourceBuckets_position_lt_of_key_lt

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBuckets
open Finset LightHistogram
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
namespace ThreeSum.SourceBuckets
theorem _root_.solution {key : ℕ → ℕ} {N i j : ℕ}
    (hi : i < N) (hj : j < N) (he : position key N i = position key N j) : i = j := by
  have hk : key i = key j := by
    rcases lt_trichotomy (key i) (key j) with h | h | h
    · have hh := position_lt_of_key_lt hi h
      omega
    · exact h
    · have hh := position_lt_of_key_lt hj h
      omega
  unfold position at he
  rw [hk] at he
  have hcount : count key (key j) i = count key (key j) j := by omega
  rcases lt_trichotomy i j with h | h | h
  · have hh := count_strict h hk
    omega
  · exact h
  · have hh := count_strict (r := key j) h rfl
    omega
end ThreeSum.SourceBuckets
