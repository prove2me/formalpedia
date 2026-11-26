-- Prove2me | solution 1 for SemigroupBetti.GenData.isSplit_exclusive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:09:47.391987+00:00
-- url     : https://prove2.me/submissions/47882359-ebd3-4c45-ac0a-9df5de72156e

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition
public import Theorems.Thm_SemigroupBetti_GenData_compSupp_disjoint
public import Theorems.Thm_SemigroupBetti_SharesVar_symm


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} {K L : Finset (Fin 4)} (hK : G.IsSplit d K) (hL : G.IsSplit d L)
    {i : Fin 4} (hiK : i ∈ K) (hiL : i ∈ L) : K = L := by
  obtain ⟨C, -, -, hC, -⟩ := hK
  obtain ⟨C', -, -, hC', -⟩ := hL
  by_contra hne
  have : C ≠ C' := by rintro rfl; exact hne (hC.symm.trans hC')
  exact Finset.disjoint_left.1 (G.compSupp_disjoint this) (hC ▸ hiK) (hC' ▸ hiL)
end SemigroupBetti.GenData
