-- Prove2me | solution 1 for SimpleGraph.ramseyBound_one_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:21.439663+00:00
-- url     : https://prove2.me/submissions/97d74a9f-a2a0-471a-99ca-0f862f457c00

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Theorems.Thm_SimpleGraph_RamseyBound_symm
public import Theorems.Thm_SimpleGraph_ramseyBound_one_left

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} {n m r s : ℕ}
namespace SimpleGraph
theorem _root_.solution (hn : 0 < n) (r : ℕ) : RamseyBound n r 1 :=
  (ramseyBound_one_left hn r).symm
end SimpleGraph
