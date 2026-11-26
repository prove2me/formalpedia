-- Prove2me | solution 1 for SemigroupBetti.GenData.dg_mul_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:54:57.497325+00:00
-- url     : https://prove2.me/submissions/04283b72-f252-4f2b-b002-6057bffc399b

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
theorem _root_.solution : G.dg * G.p = G.t := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
end SemigroupBetti.GenData
