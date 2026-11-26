-- Prove2me | solution 1 for SemigroupBetti.GenData.sideP_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:14:41.4198+00:00
-- url     : https://prove2.me/submissions/49653d48-48c0-4cf5-9c83-1100a2025a5f

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
public import Theorems.Thm_SemigroupBetti_GenData_IsSplit_compl
public import Theorems.Thm_SemigroupBetti_GenData_isSplit_of_mem_fam


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} (hd : d ∈ G.famP) : G.IsSplit d {2, 3} := by
  have hc : ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by decide
  exact hc ▸ (G.isSplit_of_mem_fam hd).compl
end SemigroupBetti.GenData
