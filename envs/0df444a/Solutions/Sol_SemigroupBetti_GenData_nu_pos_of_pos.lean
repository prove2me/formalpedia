-- Prove2me | solution 1 for SemigroupBetti.GenData.nu_pos_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:32:48.504826+00:00
-- url     : https://prove2.me/submissions/62eb1c53-0fe4-4ddb-86be-e6d421d53829

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_GenData_n_pos
public import Theorems.Thm_SemigroupBetti_GenData_single_le_nu

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {z : Fin 4 → ℕ} {i : Fin 4} (h : 0 < z i) : 0 < G.nu z :=
  lt_of_lt_of_le (Nat.mul_pos h (G.n_pos i)) (G.single_le_nu z i)
end SemigroupBetti.GenData
