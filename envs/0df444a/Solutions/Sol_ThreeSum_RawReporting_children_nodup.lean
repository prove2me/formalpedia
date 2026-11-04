-- Prove2me | solution 1 for ThreeSum.RawReporting.children_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:22:38.446253+00:00
-- url     : https://prove2.me/submissions/4a95703d-1957-43cb-a292-36440b93bcf0

import Definitions.Def_Submission_ThreeSum_RawIncidences
import Definitions.Def_Submission_ThreeSum_Reporting
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Sort
import Definitions.Def_Submission_ThreeSum_RawReporting
import Theorems.Thm_ThreeSum_RawReporting_childList_nodup

set_option autoImplicit false
open ThreeSum ThreeSum.RawReporting
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences
namespace ThreeSum.RawReporting
theorem _root_.solution {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) :
    (children q k).Nodup := by
  unfold children
  split
  · exact childList_nodup _ _
  · exact List.nodup_nil
end ThreeSum.RawReporting
