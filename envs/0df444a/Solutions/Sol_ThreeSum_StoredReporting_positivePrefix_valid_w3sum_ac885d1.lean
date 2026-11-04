-- Prove2me | solution 1 for ThreeSum.StoredReporting.positivePrefix_valid_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:36:04.653382+00:00
-- url     : https://prove2.me/submissions/fdf7b07b-67ab-4b2e-8bd4-5262ffe0fd88

import Definitions.Def_Submission_ThreeSum_BlockForced
import Definitions.Def_Submission_ThreeSum_StoredReporting
import Theorems.Thm_ThreeSum_StoredReporting_prefixRows_take
import Theorems.Thm_ThreeSum_LocalGraph_edge_data
import Theorems.Thm_ThreeSum_Reporting_mass_pos_iff


set_option autoImplicit false
open ThreeSum ThreeSum.StoredReporting
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding BlockForced
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.StoredReporting
theorem _root_.solution {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (pre : List (Finset (Fin (512 * h)))) (hk : k ≤ J)
    (hp : 0 < prefixQuery I w k pre) : ValidPrefix w.2.2 k pre := by
  obtain ⟨r, hr, hpre, _⟩ := (Reporting.mass_pos_iff (domain I w) word (fun _ => 1) k pre).mp hp
  have hw := (Finset.mem_filter.mp hr).2
  have hq : tupleOutput r.2.1 = w.2.2 := congrArg (fun w => w.2.2) hw
  constructor
  · rw [← hpre, List.length_take, word, partitionWord_length, Nat.min_eq_left hk]
  · intro i hi
    have hrows : prefixRows pre i = (edge (r.2.1 i)).val.1 := by
      rw [← hpre]
      exact prefixRows_take (fun j => (edge (r.2.1 j)).val.1) i hi
    rw [hrows]
    refine ⟨?_, (edge_data (edge (r.2.1 i))).1⟩
    have he : output (edge (r.2.1 i)) = outputRows w.2.2 i :=
      congrArg (fun q => (q i).2.val) hq
    rw [← he]
    exact Finset.subset_union_left
end ThreeSum.StoredReporting
