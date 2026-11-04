-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.rootCeiling_sq_le_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:19.367862+00:00
-- url     : https://prove2.me/submissions/de2d427b-cbc7-4a74-a7f0-76ea39840bb6

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
theorem _root_.solution {N : ℕ} (hN : 0 < N) : rootCeiling N ^ 2 ≤ 4 * N := by
  have hmono := Nat.sqrt_le_sqrt (Nat.sub_le N 1)
  have hpos := Nat.sqrt_pos.mpr hN
  have hlo := Nat.sqrt_le' N
  have hroot : rootCeiling N ≤ 2 * Nat.sqrt N := by
    unfold rootCeiling
    omega
  have hsq := Nat.pow_le_pow_left hroot 2
  nlinarith
end ThreeSum.LocalCoverBounds
