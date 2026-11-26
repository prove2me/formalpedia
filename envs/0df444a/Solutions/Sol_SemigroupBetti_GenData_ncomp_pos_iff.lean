-- Prove2me | solution 1 for SemigroupBetti.GenData.ncomp_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:34:19.18215+00:00
-- url     : https://prove2.me/submissions/81b8501a-5360-4090-a7e8-944a7642b2db

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber
public import Theorems.Thm_SemigroupBetti_GenData_ncomp_eq_zero_iff

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} : 0 < G.ncomp d ↔ (G.fiber d).Nonempty := by
  rw [Nat.pos_iff_ne_zero, Ne, ncomp_eq_zero_iff, ← Ne, ← Finset.nonempty_iff_ne_empty]
end SemigroupBetti.GenData
