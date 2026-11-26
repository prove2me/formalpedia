-- Prove2me | solution 1 for SemigroupBetti.GenData.n_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:25:26.768416+00:00
-- url     : https://prove2.me/submissions/cca609a5-7c4f-4998-a729-f0d3e1f0b30e

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
theorem _root_.solution : G.n 1 = G.m + G.a := rfl
end SemigroupBetti.GenData
