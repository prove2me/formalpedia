-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_5_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:19.546243+00:00
-- url     : https://prove2.me/submissions/99ed9122-dbea-4253-8d85-2173fb817053

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (d : ℕ → Pomega) (x : Pomega) :
    representClosure d (representClosure d x) = representClosure d x := by
  ext m
  constructor
  · intro hm i hi
    obtain ⟨k, hk, hik⟩ := Set.mem_iUnion₂.mp (hm hi)
    exact hk hik
  · intro hm i hi
    exact Set.mem_iUnion₂.mpr ⟨m, hm, hi⟩
end Scott1976.DataTypesAsLattices
