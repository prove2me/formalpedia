-- Prove2me | solution 1 for SemigroupBetti.GenData.exists_supp_eq_of_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:13:01.119117+00:00
-- url     : https://prove2.me/submissions/d9dfa676-3bc4-4675-a61b-0a8463aa7699

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition
public import Theorems.Thm_SemigroupBetti_GenData_exists_supp_eq
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
attribute [local simp] SemigroupBetti.GenData.mem_fiber



set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} {K : Finset (Fin 4)} (hS : G.IsSplit d K)
    (hK : K.card = 2) : ∃ z : Fin 4 → ℕ, G.nu z = d ∧ supp z = K := by
  obtain ⟨C, -, -, hC, -⟩ := hS
  obtain ⟨z, -, hz⟩ := G.exists_supp_eq hK hC
  exact ⟨z.1, G.mem_fiber.1 z.2, hz⟩
end SemigroupBetti.GenData
