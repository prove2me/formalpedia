-- Prove2me | solution 1 for ThreeSum.TernaryCoverRetained.occurrence_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:46:14.544219+00:00
-- url     : https://prove2.me/submissions/0b733ee8-2a98-4050-a3da-1338bdc481f9

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverRetained
open Finset
open scoped BigOperators
variable {E A B K : Type*} [Fintype E]
variable [DecidableEq A] [DecidableEq B] [DecidableEq K]
namespace ThreeSum.TernaryCoverRetained
theorem _root_.solution {C I : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq C] (s : Finset C) (occurrence : C → I) (cap : ℕ)
    (hcap : ∀ i : I, (s.filter fun c => occurrence c = i).card ≤ cap) :
    s.card ≤ Fintype.card I * cap := by
  classical
  calc
    s.card = ∑ i : I, (s.filter fun c => occurrence c = i).card :=
      card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
    _ ≤ ∑ _i : I, cap := sum_le_sum (fun i _ => hcap i)
    _ = Fintype.card I * cap := by simp
end ThreeSum.TernaryCoverRetained
