-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.selectedPrime_gt_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:31.572171+00:00
-- url     : https://prove2.me/submissions/9882d708-ee39-4bac-889b-4bd578651d78

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

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution {N : ℕ} (hN : 1 < N) : 2 < selectedPrime N := by
  have hs : 0 < Nat.sqrt (N - 1) := Nat.sqrt_pos.mpr (by omega)
  have hlo := (selectedPrime_spec N).2.1
  unfold rootCeiling at hlo
  omega
end ThreeSum.LocalCoverBounds
