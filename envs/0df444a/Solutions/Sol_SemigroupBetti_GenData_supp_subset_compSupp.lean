-- Prove2me | solution 1 for SemigroupBetti.GenData.supp_subset_compSupp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:55:46.365034+00:00
-- url     : https://prove2.me/submissions/76d42400-ce0d-4034-8871-14cd330a898d

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber
public import Theorems.Thm_SemigroupBetti_GenData_mem_compSupp
public import Theorems.Thm_SemigroupBetti_mem_supp
attribute [local simp] SemigroupBetti.mem_supp



set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} (z : G.fiber d) :
    supp z.1 ⊆ G.compSupp ((G.nabla d).connectedComponentMk z) := by
  intro i hi; rw [mem_supp] at hi; exact G.mem_compSupp.2 ⟨z, rfl, hi⟩
end SemigroupBetti.GenData
