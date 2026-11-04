-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.localPrime_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:15:15.39359+00:00
-- url     : https://prove2.me/submissions/f4a12876-7c2c-4c65-a421-5bfec188a07f

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
import Theorems.Thm_ThreeSum_LocalCoverBounds_selectedPrime_odd
import Theorems.Thm_ThreeSum_LocalCoverBounds_localThreshold_gt_one

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution {h : ℕ} (hh : 0 < h) : Odd (localPrime h) :=
  selectedPrime_odd (localThreshold_gt_one hh)
end ThreeSum.LocalCoverBounds
