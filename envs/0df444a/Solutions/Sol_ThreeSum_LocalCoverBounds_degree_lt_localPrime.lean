-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.degree_lt_localPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:22:54.095178+00:00
-- url     : https://prove2.me/submissions/4f01be13-96f5-48d2-84aa-b91ebe3e4903

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
import Theorems.Thm_ThreeSum_LocalCoverBounds_degree_lt_modulus
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_sq_lower

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution {h : ℕ} (hh : 0 < h) :
    degree (512 * h) h < localPrime h :=
  degree_lt_modulus hh (by omega) (localPrime_sq_lower h)
end ThreeSum.LocalCoverBounds
