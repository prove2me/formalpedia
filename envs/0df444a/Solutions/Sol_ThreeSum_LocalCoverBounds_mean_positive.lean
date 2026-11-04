-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.mean_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:16.627768+00:00
-- url     : https://prove2.me/submissions/bd546751-547c-4f20-8073-8bd76816d7b3

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
theorem _root_.solution {L h p : ℕ} (hL : 2 * h ≤ L) (hp : 0 < p) :
    0 < mean L h p := by
  have hM : 0 < outputCount L h := Nat.choose_pos hL
  have hG : 0 < groupSize h := Nat.choose_pos (by omega)
  unfold mean
  positivity
end ThreeSum.LocalCoverBounds
