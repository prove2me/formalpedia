-- Prove2me | solution 1 for ThreeSum.LocalHashMoments.mem_allWeights
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:25:26.191818+00:00
-- url     : https://prove2.me/submissions/2670fbe6-2227-4d94-b381-3b38ee48d362

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
theorem _root_.solution (values : List K) (hvalues : ∀ x, x ∈ values)
    (w : Weight L K) : w ∈ allWeights L values := by
  apply List.mem_map.mpr
  refine ⟨(fun i _ => w i), ?_, rfl⟩
  exact (List.mem_pi _ _).mpr (fun i hi => hvalues (w i))
end ThreeSum.LocalHashMoments
