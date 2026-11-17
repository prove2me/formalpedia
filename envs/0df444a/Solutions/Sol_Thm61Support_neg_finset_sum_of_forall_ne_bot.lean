-- Prove2me | solution 1 for Thm61Support.neg_finset_sum_of_forall_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:07:34.563771+00:00
-- url     : https://prove2.me/submissions/64630cd3-01c9-4f8a-abe7-c7d82ea4405e

import Theorems.Thm_Thm61Support_finset_sum_ne_bot_of_forall_ne_bot
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F001
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]
namespace Thm61Support
end Thm61Support
section Thm61Support
open Thm61Support

theorem solution {ι : Type*} (s : Finset ι) (f : ι → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊥) :
    Finset.sum s (fun i => -(f i)) = -(Finset.sum s f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have hfi : f i ≠ ⊥ := hf i (Finset.mem_insert_self i s)
      have hs : Finset.sum s f ≠ ⊥ := by
        exact finset_sum_ne_bot_of_forall_ne_bot s f
          (fun j hj => hf j (Finset.mem_insert.mpr (Or.inr hj)))
      rw [EReal.neg_add (.inl hfi) (.inr hs)]
      exact congrArg (fun t => -f i + t) <|
        ih (fun j hj => hf j (Finset.mem_insert.mpr (Or.inr hj)))
end Thm61Support
