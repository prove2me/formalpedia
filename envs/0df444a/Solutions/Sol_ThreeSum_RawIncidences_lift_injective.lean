-- Prove2me | solution 1 for ThreeSum.RawIncidences.lift_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:17:49.280117+00:00
-- url     : https://prove2.me/submissions/1c043e4e-2033-46fa-80f6-e38472999b2f

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
theorem _root_.solution : Function.Injective lift := by
  intro i j hij
  apply Fin.ext
  unfold lift at hij
  omega
end ThreeSum.RawIncidences
