-- Prove2me | solution 1 for SemigroupBetti.GenData.g_dvd_w
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:27:10.737898+00:00
-- url     : https://prove2.me/submissions/6612df09-37f1-48e2-8ff8-bb7e9e8e99f0

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
theorem _root_.solution : G.g ∣ G.w := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
end SemigroupBetti.GenData
