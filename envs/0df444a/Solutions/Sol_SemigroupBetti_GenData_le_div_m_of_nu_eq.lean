-- Prove2me | solution 1 for SemigroupBetti.GenData.le_div_m_of_nu_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:33:01.325695+00:00
-- url     : https://prove2.me/submissions/f42c0530-6a0c-4665-8ff3-4d15c32107b1

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber
public import Theorems.Thm_SemigroupBetti_GenData_m_mul_le_nu


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {z : Fin 4 → ℕ} {d : ℕ} (h : G.nu z = d) (i : Fin 4) :
    z i ≤ d / G.m := by
  rw [Nat.le_div_iff_mul_le G.m_pos, mul_comm, ← h]; exact G.m_mul_le_nu z i
end SemigroupBetti.GenData
