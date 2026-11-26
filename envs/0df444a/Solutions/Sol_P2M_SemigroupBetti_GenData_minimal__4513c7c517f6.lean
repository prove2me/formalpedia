-- Prove2me | solution 1 for P2M_SemigroupBetti_GenData_minimal__4513c7c517f6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:32:25.134327+00:00
-- url     : https://prove2.me/submissions/e0e80037-2919-4341-9b3b-cc396044f245

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
theorem _root_.solution (i : Fin 4) (z : Fin 4 → ℕ) (hz : z i = 0) : G.nu z ≠ G.n i :=
  G.minimal i z hz
end SemigroupBetti.GenData
