-- Prove2me | solution 1 for SemigroupBetti.GenData.n_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:25:39.949172+00:00
-- url     : https://prove2.me/submissions/21478886-abae-442d-a090-5d2830516410

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
theorem _root_.solution : G.n 2 = G.m + G.b := rfl
end SemigroupBetti.GenData
