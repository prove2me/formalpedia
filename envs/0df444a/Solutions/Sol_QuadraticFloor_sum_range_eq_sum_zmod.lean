-- Prove2me | solution 1 for QuadraticFloor.sum_range_eq_sum_zmod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:43:46.934208+00:00
-- url     : https://prove2.me/submissions/925b5657-364b-45a8-8202-a01920a3ebf6

module
public import Definitions.Def_QuadraticFloor_Defs
public import Definitions.Def_QuadraticFloor_RootCount

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution {M : Type*} [AddCommMonoid M] (G : ZMod p → M) :
    ∑ n ∈ range p, G n = ∑ x : ZMod p, G x := by
  refine sum_nbij' (fun n => (n : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intro n _; exact mem_univ _
  · intro x _; simpa using x.val_lt
  · intro n hn; simpa using ZMod.val_cast_of_lt (mem_range.1 hn)
  · intro x _; simp
  · intro n _; rfl
end QuadraticFloor
