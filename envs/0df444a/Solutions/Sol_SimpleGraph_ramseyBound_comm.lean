-- Prove2me | solution 1 for SimpleGraph.ramseyBound_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:00.950264+00:00
-- url     : https://prove2.me/submissions/1c48df41-8981-46f8-b321-bc6b9be736be

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Theorems.Thm_SimpleGraph_RamseyBound_symm

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} {n m r s : ℕ}
namespace SimpleGraph
theorem _root_.solution : RamseyBound n r s ↔ RamseyBound n s r := ⟨.symm, .symm⟩
end SimpleGraph
