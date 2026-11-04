-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.localBucketCap_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:22:58.35442+00:00
-- url     : https://prove2.me/submissions/eb600769-ceef-4ab3-b9f4-d53b19a3c957

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
import Theorems.Thm_ThreeSum_LocalCoverBounds_bucketCap_threshold
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution (h : ℕ) :
    4 * (localPrime h + vertexCount (512 * h) h) ≤ localBucketCap h * localPrime h :=
  bucketCap_threshold (localPrime_pos h)
end ThreeSum.LocalCoverBounds
