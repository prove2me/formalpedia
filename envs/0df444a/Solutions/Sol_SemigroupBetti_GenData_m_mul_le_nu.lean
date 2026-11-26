-- Prove2me | solution 1 for SemigroupBetti.GenData.m_mul_le_nu
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:31:22.216053+00:00
-- url     : https://prove2.me/submissions/63a8e492-ae75-4728-acfc-11553dffdeda

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_GenData_m_le_n
public import Theorems.Thm_SemigroupBetti_GenData_single_le_nu

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution (z : Fin 4 → ℕ) (i : Fin 4) : G.m * z i ≤ G.nu z := by
  calc G.m * z i ≤ z i * G.n i := by rw [mul_comm]; exact Nat.mul_le_mul_left _ (G.m_le_n i)
    _ ≤ G.nu z := G.single_le_nu z i
end SemigroupBetti.GenData
