-- Prove2me | solution 1 for SemigroupBetti.GenData.g_dvd_b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:27:06.135436+00:00
-- url     : https://prove2.me/submissions/1df45326-0711-4cc9-b401-d9d06c50b6cc

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
theorem _root_.solution : G.g ∣ G.b := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
end SemigroupBetti.GenData
