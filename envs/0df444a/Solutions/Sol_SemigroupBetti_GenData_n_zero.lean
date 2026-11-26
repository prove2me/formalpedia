-- Prove2me | solution 1 for SemigroupBetti.GenData.n_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:25:54.231889+00:00
-- url     : https://prove2.me/submissions/caefc09d-58bf-4f3f-9d11-7076111d36b1

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : G.n 0 = G.m := rfl
end SemigroupBetti.GenData
