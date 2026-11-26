-- Prove2me | solution 1 for SemigroupBetti.GenData.dg_mul_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:55:07.537103+00:00
-- url     : https://prove2.me/submissions/4f0ba08b-d66b-4be6-b69f-33da04ac4947

module
public import Definitions.Def_SemigroupBetti_Partition
public import Definitions.Def_SemigroupBetti_Identities

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : G.dg * G.q = G.s := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
end SemigroupBetti.GenData
