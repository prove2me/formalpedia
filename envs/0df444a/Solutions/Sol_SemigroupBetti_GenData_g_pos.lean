-- Prove2me | solution 1 for SemigroupBetti.GenData.g_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:26:33.047253+00:00
-- url     : https://prove2.me/submissions/28dc40c2-a0df-4e9a-aceb-c59c99873052

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
theorem _root_.solution : 0 < G.g := Nat.gcd_pos_of_pos_left _ G.a_pos
end SemigroupBetti.GenData
