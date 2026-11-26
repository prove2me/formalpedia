-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.e_or_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:53:59.502534+00:00
-- url     : https://prove2.me/submissions/81736a81-b74c-434d-8d61-1db8d6b08f92

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Theorems.Thm_Scott1976_DataTypesAsLattices_e_or

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {n m : ℕ} {x : Pomega} (hn : e n ⊆ x) (hm : e m ⊆ x) :
    e (n ||| m) ⊆ x := by
  rw [e_or]
  exact Set.union_subset hn hm
end Scott1976.DataTypesAsLattices
