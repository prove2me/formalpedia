-- Prove2me | solution 1 for ThreeSum.RawReporting.total_frontier_length_le_rawMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:58:52.993195+00:00
-- url     : https://prove2.me/submissions/50d79b23-941c-4679-bc57-1b62df3f30de

import Definitions.Def_Submission_ThreeSum_RawIncidences
import Definitions.Def_Submission_ThreeSum_Reporting
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Sort
import Definitions.Def_Submission_ThreeSum_RawReporting
import Theorems.Thm_ThreeSum_RawReporting_total_frontier_length_le_raw_card

set_option autoImplicit false
open ThreeSum ThreeSum.RawReporting
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.RawReporting
theorem _root_.solution {h J k : ℕ} (P d : ℤ)
    (T : Finset (Original α β γ)) (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (hk : k ≤ J) :
    (∑ w : Wanted h J α, (frontier (rawOn h J P d T a b c) w k).length) ≤
      rawMass h J P d T a b c :=
  total_frontier_length_le_raw_card _ hk
end ThreeSum.RawReporting
