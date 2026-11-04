-- Prove2me | solution 1 for ThreeSum.RawReporting.total_frontier_length_le_raw_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:54:58.323085+00:00
-- url     : https://prove2.me/submissions/1006748c-ec51-42f7-bbe0-395a49cad64a

import Definitions.Def_Submission_ThreeSum_RawIncidences
import Definitions.Def_Submission_ThreeSum_Reporting
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Sort
import Definitions.Def_Submission_ThreeSum_RawReporting
import Theorems.Thm_ThreeSum_RawReporting_frontier_length_le_domain

set_option autoImplicit false
open ThreeSum ThreeSum.RawReporting
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.RawReporting
theorem _root_.solution {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (hk : k ≤ J) : (∑ w : Wanted h J α, (frontier I w k).length) ≤ I.card := by
  calc
    _ ≤ ∑ w : Wanted h J α, (domain I w).card := by
      apply Finset.sum_le_sum
      intro w _
      exact frontier_length_le_domain I w hk
    _ = _ := by
      symm
      exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
end ThreeSum.RawReporting
