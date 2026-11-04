-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.selectedPrime_sq_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:30.430196+00:00
-- url     : https://prove2.me/submissions/0717507c-794d-46ca-aec3-d3338586384a

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
import Theorems.Thm_ThreeSum_LocalCoverBounds_rootCeiling_sq_le_four
import Theorems.Thm_ThreeSum_LocalCoverBounds_selectedPrime_spec

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution {N : ℕ} (hN : 0 < N) :
    selectedPrime N ^ 2 ≤ 16 * N := by
  have hu := (selectedPrime_spec N).2.2
  have hsq := Nat.pow_le_pow_left hu 2
  have hr := rootCeiling_sq_le_four hN
  nlinarith
end ThreeSum.LocalCoverBounds
