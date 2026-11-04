-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.selectedPrime_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:20.412812+00:00
-- url     : https://prove2.me/submissions/2f5b5c6d-c7fb-4429-95f3-82d5d15dbe8d

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution (N : ℕ) :
    Nat.Prime (selectedPrime N) ∧ rootCeiling N < selectedPrime N ∧
      selectedPrime N ≤ 2 * rootCeiling N :=
  mem_primeCandidates.mp (Finset.min'_mem _ _)
end ThreeSum.LocalCoverBounds
