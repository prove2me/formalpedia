-- Prove2me | solution 1 for ThreeSum.Cover.incidence_card_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:07:14.360197+00:00
-- url     : https://prove2.me/submissions/0d7a9097-16f7-492e-a462-f926044975ee

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Cover

set_option autoImplicit false
open ThreeSum ThreeSum.Cover
open Finset
open scoped BigOperators
namespace ThreeSum.Cover
theorem _root_.solution {Ω U : Type*} [Fintype Ω] [DecidableEq U]
    (targets : Finset U) (covers : Ω → U → Prop)
    [DecidableRel covers] :
    (∑ ω, (targets.filter (covers ω)).card) =
      ∑ u ∈ targets, (univ.filter fun ω => covers ω u).card := by
  simp_rw [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
end ThreeSum.Cover
