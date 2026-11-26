-- Prove2me | solution 1 for SemigroupBetti.GenData.sel_le_of_coords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:16:56.674459+00:00
-- url     : https://prove2.me/submissions/6f656199-0b8b-4068-bc33-223f9b1e678e

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
public import Theorems.Thm_SemigroupBetti_GenData_sel_eq_zero


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {K : Finset (Fin 4)} {i k : Fin 4} (hKe : K = {i, k}) (hK : K.card = 2)
    {d d' : ℕ} (hS : G.IsSplit d K) (hS' : G.IsSplit d' K)
    (hi : G.sel d K i ≤ G.sel d' K i) (hk : G.sel d K k ≤ G.sel d' K k) :
    G.sel d K ≤ G.sel d' K := by
  intro j
  by_cases hj : j ∈ K
  · rw [hKe, mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact hi
    · exact hk
  · rw [G.sel_eq_zero hS hK hj, G.sel_eq_zero hS' hK hj]
end SemigroupBetti.GenData
