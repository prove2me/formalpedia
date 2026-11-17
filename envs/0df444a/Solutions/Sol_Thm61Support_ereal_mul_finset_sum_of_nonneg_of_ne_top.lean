-- Prove2me | solution 1 for Thm61Support.ereal_mul_finset_sum_of_nonneg_of_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:04:26.48485+00:00
-- url     : https://prove2.me/submissions/a91563aa-ef89-41ce-b832-f662a9160687

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

theorem solution {ι : Type*} (s : Finset ι)
    {a : EReal} (ha : 0 ≤ a) (ha_top : a ≠ ⊤) (f : ι → EReal) :
    a * (Finset.sum s f) = Finset.sum s (fun i => a * f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      rw [EReal.left_distrib_of_nonneg_of_ne_top ha ha_top]
      exact congrArg (fun t => a * f i + t) ih
end Thm61Support
