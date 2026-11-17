-- Prove2me | solution 1 for Thm61Support.finset_sum_ne_top_of_forall_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:04:43.256555+00:00
-- url     : https://prove2.me/submissions/ddedd2bd-381e-4afd-8124-97813b693ca3

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
    Finset.sum s f ≠ ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact EReal.add_ne_top (hf i (by simp [hi])) <|
        ih (fun j hj => hf j (by simp [hj]))
end Thm61Support
