-- Prove2me | solution 1 for SemigroupBetti.GenData.W_le_w
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:33:40.76362+00:00
-- url     : https://prove2.me/submissions/196e7b07-0497-440d-9af3-6ebb8c6feae1

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_GenData_g_pos
public import Theorems.Thm_SemigroupBetti_GenData_w_eq

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : G.W ≤ G.w := by
  rw [G.w_eq]; exact Nat.le_mul_of_pos_left _ G.g_pos
end SemigroupBetti.GenData
