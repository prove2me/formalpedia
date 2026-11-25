-- Prove2me | solution 1 for SimpleGraph.cliqueCountIn_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:42:57.638405+00:00
-- url     : https://prove2.me/submissions/fdfbded7-095a-4b23-b48f-59ff9526dc21

module
public import Definitions.Def_GoodmanSupersaturation_Goodman
public import Mathlib.Tactic.Rify
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_GoodmanSupersaturation_Supersaturation
public import Theorems.Thm_SimpleGraph_cliqueCountIn_univ
public import Theorems.Thm_SimpleGraph_degreeWithin_univ
attribute [local simp] SimpleGraph.cliqueCountIn_univ
attribute [local simp] SimpleGraph.degreeWithin_univ



set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*}
variable [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution (S : Finset V) : G.cliqueCountIn S 1 = #S := by
  rw [cliqueCountIn, filter_true_of_mem fun T hT => ?_, card_powersetCard, Nat.choose_one_right]
  obtain ⟨a, rfl⟩ := card_eq_one.mp (mem_powersetCard.mp hT).2
  simp
end SimpleGraph
