-- Prove2me | solution 1 for ThreeSum.RawIncidences.ofFn_tupleOfList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:21:16.783231+00:00
-- url     : https://prove2.me/submissions/a1028781-b20c-422b-8ceb-25c6e24ad770

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences

set_option autoImplicit false
open ThreeSum ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds
namespace ThreeSum.RawIncidences
theorem _root_.solution {h J : ℕ} (xs : List (RetainedChoice h)) (hlen : xs.length = J) :
    List.ofFn (tupleOfList xs hlen) = xs := by
  subst J
  exact List.ofFn_get xs
end ThreeSum.RawIncidences
