-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.localPrime_sq_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:19:56.475525+00:00
-- url     : https://prove2.me/submissions/bf2d234f-6b1e-43ae-a9a8-973058ecbff5

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
import Theorems.Thm_ThreeSum_LocalCoverBounds_selectedPrime_sq_upper
import Theorems.Thm_ThreeSum_LocalCoverBounds_localThreshold_pos

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution (h : ℕ) :
    localPrime h ^ 2 ≤ 16 * (outputCount (512 * h) h * 2 ^ (2 * h)) :=
  selectedPrime_sq_upper (localThreshold_pos h)
end ThreeSum.LocalCoverBounds
