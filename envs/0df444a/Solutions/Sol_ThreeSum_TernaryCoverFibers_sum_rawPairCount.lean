-- Prove2me | solution 1 for ThreeSum.TernaryCoverFibers.sum_rawPairCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:45:16.059809+00:00
-- url     : https://prove2.me/submissions/8d508a9c-3869-4a90-865b-11cecff087e8

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverFibers
open Finset
open scoped BigOperators
variable {E Q K : Type*} [Fintype E] [Fintype Q] [Fintype K]
variable [DecidableEq Q] [DecidableEq K] [AddCommGroup K]
namespace ThreeSum.TernaryCoverFibers
theorem _root_.solution (left right : E → K) (o : K) :
    (∑ a : K, rawPairCount left right a (o - a)) =
      (univ.filter fun e => left e + right e = o).card := by
  classical
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := univ.filter fun e => left e + right e = o)
    (t := (univ : Finset K)) (f := left) (fun _ _ => mem_univ _)
  rw [hpartition]
  apply sum_congr rfl
  intro a _
  unfold rawPairCount
  congr 1
  ext e
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hl, hr⟩
    exact ⟨by rw [hl, hr]; simp, hl⟩
  · rintro ⟨hadd, hl⟩
    exact ⟨hl, by rw [← hadd, hl]; simp⟩
end ThreeSum.TernaryCoverFibers
