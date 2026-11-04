-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.badCount_le_localPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:15:16.495553+00:00
-- url     : https://prove2.me/submissions/6dc2fc80-dad1-4509-a725-a242be60cfc2

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
import Theorems.Thm_ThreeSum_LocalCoverBounds_degree_lt_localPrime
import Theorems.Thm_ThreeSum_LocalCoverBounds_groupSize_lt_localPrime

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution {h : ℕ} (hh : 0 < h) :
    2 * degree (512 * h) h + groupSize h ≤ 3 * localPrime h := by
  have hd := degree_lt_localPrime hh
  have hg := groupSize_lt_localPrime hh
  omega
end ThreeSum.LocalCoverBounds
