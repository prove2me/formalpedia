-- Prove2me | solution 1 for SemigroupBetti.GenData.gcd_m_g
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:33:28.674106+00:00
-- url     : https://prove2.me/submissions/05500c8b-b0ab-49b7-8bbe-ede41e59ad50

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
theorem _root_.solution : Nat.gcd G.m G.g = 1 := G.gcd_eq_one
end SemigroupBetti.GenData
