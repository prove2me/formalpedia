-- Prove2me | solution 1 for ThreeSum.Cover.survivor_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:07:15.843733+00:00
-- url     : https://prove2.me/submissions/2448bcd4-4a03-4255-b598-71fab096f940

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
theorem _root_.solution {U : Type*} [DecidableEq U]
    (targets : Finset U) (covers : U → Prop) [DecidablePred covers]
    (a : ℕ) (ha : 0 < a)
    (hgood : targets.card ≤ a * (targets.filter covers).card) :
    a * (targets.filter fun u => ¬ covers u).card ≤ (a - 1) * targets.card := by
  have hc := card_filter_add_card_filter_not (s := targets) (p := covers)
  have ha' : a - 1 + 1 = a := by omega
  nlinarith
end ThreeSum.Cover
