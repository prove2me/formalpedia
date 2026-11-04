-- Prove2me | solution 1 for ThreeSum.SubsetAddress.weight_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:36:21.139969+00:00
-- url     : https://prove2.me/submissions/a1f201b6-4a99-4a9a-afe8-d792fb2c203b

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Embedding
import Mathlib.Combinatorics.Colex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_SubsetAddress

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution (L : ℕ) : weight L 0 = 0 := by
  induction L with
  | zero => rfl
  | succ L ih => simpa [weight, Nat.two_pow_pos] using ih
end ThreeSum.SubsetAddress
