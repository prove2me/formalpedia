-- Prove2me | solution 1 for SemigroupBetti.GenData.n_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:25:42.303678+00:00
-- url     : https://prove2.me/submissions/2687f5fa-8076-4493-a973-612c15e2d4b5

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
theorem _root_.solution : G.n 3 = G.m + G.w := rfl
end SemigroupBetti.GenData
