-- Prove2me | solution 1 for SemigroupBetti.GenData.g_dvd_a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:26:56.622867+00:00
-- url     : https://prove2.me/submissions/e39f7275-d59b-423a-827e-b423b418412f

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
theorem _root_.solution : G.g ∣ G.a := Nat.gcd_dvd_left _ _
end SemigroupBetti.GenData
