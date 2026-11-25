-- Prove2me | solution 1 for SimpleGraph.ramseyBound_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:07.424585+00:00
-- url     : https://prove2.me/submissions/30139441-91bc-4f4b-87cb-b45271e1d82f

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Theorems.Thm_SimpleGraph_RamseyBound_symm
public import Theorems.Thm_SimpleGraph_ramseyBound_zero_left

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} {n m r s : ℕ}
namespace SimpleGraph
theorem _root_.solution (n r : ℕ) : RamseyBound n r 0 := (ramseyBound_zero_left n r).symm
end SimpleGraph
