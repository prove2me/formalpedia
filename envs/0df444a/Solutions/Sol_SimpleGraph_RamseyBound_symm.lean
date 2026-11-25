-- Prove2me | solution 1 for SimpleGraph.RamseyBound.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:25:50.846282+00:00
-- url     : https://prove2.me/submissions/bec14418-24db-48f7-9770-23e6643acb56

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Definitions.Def_RamseyReservoir_RamseyBound

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} {n m r s : ℕ}
namespace SimpleGraph
namespace RamseyBound
theorem _root_.solution (h : RamseyBound n r s) : RamseyBound n s r := fun G => by
  simpa using (h Gᶜ).symm
end RamseyBound
end SimpleGraph
