-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.eq_5_16
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:55:39.548552+00:00
-- url     : https://prove2.me/submissions/2de9abe0-8db2-4f0c-aa2d-590b4ad91946

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (a x : Pomega) : x ⊆ Vapply a x := by
  intro k hk y hy
  exact hy.1 hk
end Scott1976.DataTypesAsLattices
