-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.singleton_eq_e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:02:49.898738+00:00
-- url     : https://prove2.me/submissions/3ba24927-8eeb-405e-9298-3ec119ca73e2

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Theorems.Thm_Scott1976_DataTypesAsLattices_e_pow2

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (k : ℕ) : ({k} : Pomega) = e (2 ^ k) := (e_pow2 k).symm
end Scott1976.DataTypesAsLattices
