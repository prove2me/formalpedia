-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.selectedPrime_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:19:52.271905+00:00
-- url     : https://prove2.me/submissions/662fca80-7cab-4d32-874d-0ec83c1bf05c

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
import Theorems.Thm_ThreeSum_LocalCoverBounds_selectedPrime_spec
import Theorems.Thm_ThreeSum_LocalCoverBounds_selectedPrime_gt_two

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution {N : ℕ} (hN : 1 < N) : Odd (selectedPrime N) :=
  (selectedPrime_spec N).1.odd_of_ne_two (by have := selectedPrime_gt_two hN; omega)
end ThreeSum.LocalCoverBounds
