-- Prove2me | solution 1 for SemigroupBetti.GenData.mono_sub_mem_toricKer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:08:06.979365+00:00
-- url     : https://prove2.me/submissions/600b81cd-2824-4d10-a735-68459883a664

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
public import Theorems.Thm_SemigroupBetti_GenData_toricMap_mono
public import Theorems.Thm_SemigroupBetti_GenData_mem_toricKer

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (G : GenData) (K : Type*) [Field K]
namespace SemigroupBetti.GenData
theorem _root_.solution {z z' : Fin 4 → ℕ} (h : G.nu z = G.nu z') :
    mono K z - mono K z' ∈ G.toricKer K := by
  rw [mem_toricKer, map_sub, toricMap_mono, toricMap_mono, h, sub_self]
end SemigroupBetti.GenData
