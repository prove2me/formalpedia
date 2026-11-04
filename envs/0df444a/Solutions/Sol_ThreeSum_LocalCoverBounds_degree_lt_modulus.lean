-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.degree_lt_modulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:19:51.17013+00:00
-- url     : https://prove2.me/submissions/5af2c7df-d553-4b65-8357-47a2dfe26dac

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
import Theorems.Thm_ThreeSum_LocalCoverBounds_degree_sq_lt_output_pow

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution {L h p : ℕ} (hh : 0 < h) (hL : 2 * h ≤ L)
    (hp : outputCount L h * 2 ^ (2 * h) ≤ p ^ 2) : degree L h < p := by
  have hs := (degree_sq_lt_output_pow hh hL).trans_le hp
  nlinarith
end ThreeSum.LocalCoverBounds
