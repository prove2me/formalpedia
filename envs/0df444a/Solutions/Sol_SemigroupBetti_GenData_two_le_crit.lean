-- Prove2me | solution 1 for SemigroupBetti.GenData.two_le_crit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:17:32.406864+00:00
-- url     : https://prove2.me/submissions/cbaa74bd-d693-443e-bb96-07bc52cea2ab

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Critical
public import Theorems.Thm_SemigroupBetti_GenData_one_le_crit
public import Theorems.Thm_SemigroupBetti_GenData_exists_alt
public import Theorems.Thm_SemigroupBetti_GenData_alt_coord_eq_zero
public import Theorems.Thm_P2M_SemigroupBetti_GenData_minimal__4513c7c517f6


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution (i : Fin 4) : 2 ≤ G.crit i := by
  by_contra h
  have h1 : G.crit i = 1 := by have := G.one_le_crit i; omega
  obtain ⟨y, hy, hyne⟩ := G.exists_alt i
  have hyi := G.alt_coord_eq_zero hy hyne
  rw [h1, one_mul] at hy
  exact G.minimal' i y hyi hy
end SemigroupBetti.GenData
