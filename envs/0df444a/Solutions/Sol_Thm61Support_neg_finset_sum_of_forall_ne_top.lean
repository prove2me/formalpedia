-- Prove2me | solution 1 for Thm61Support.neg_finset_sum_of_forall_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:07:42.933692+00:00
-- url     : https://prove2.me/submissions/a0d0d745-3501-4d2c-97f9-bdee0e5a40f8

import Theorems.Thm_Thm61Support_finset_sum_ne_top_of_forall_ne_top
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
    (hf : ∀ i ∈ s, f i ≠ ⊤) :
    Finset.sum s (fun i => -(f i)) = -(Finset.sum s f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have hfi : f i ≠ ⊤ := hf i (Finset.mem_insert_self i s)
      have hs : Finset.sum s f ≠ ⊤ := by
        exact finset_sum_ne_top_of_forall_ne_top s f
          (fun j hj => hf j (Finset.mem_insert.mpr (Or.inr hj)))
      rw [EReal.neg_add (.inr hs) (.inl hfi)]
      exact congrArg (fun t => -f i + t) <|
        ih (fun j hj => hf j (Finset.mem_insert.mpr (Or.inr hj)))
end Thm61Support
