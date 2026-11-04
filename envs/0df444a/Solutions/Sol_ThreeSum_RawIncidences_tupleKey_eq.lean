-- Prove2me | solution 1 for ThreeSum.RawIncidences.tupleKey_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:30:06.471947+00:00
-- url     : https://prove2.me/submissions/3f76420c-6d2a-42a7-b2ba-287b4ef40a87

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Theorems.Thm_ThreeSum_GlobalEncoding_positionalHash_difference


set_option autoImplicit false
open ThreeSum ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds
namespace ThreeSum.RawIncidences
theorem _root_.solution {h J : ℕ} (t : ChoiceTuple h J) :
    tupleKey t = tupleRight t - tupleLeft t := by
  rw [tupleKey, globalKey, tupleRight, tupleLeft, positionalHash_difference]
  congr 1
  exact List.map_ofFn.symm
end ThreeSum.RawIncidences
