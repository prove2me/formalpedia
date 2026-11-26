-- Prove2me | solution 1 for SemigroupBetti.GenData.sideQ_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:05:34.952001+00:00
-- url     : https://prove2.me/submissions/0c403b9f-6008-480f-94fb-3153a6860d0a

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
theorem _root_.solution {d : ℕ} (hd : d ∈ G.famQ) : G.IsSplit d {1, 3} := by
  have hc : ({0, 2} : Finset (Fin 4))ᶜ = {1, 3} := by decide
  exact hc ▸ (G.isSplit_of_mem_fam hd).compl
end SemigroupBetti.GenData
