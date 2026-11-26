-- Prove2me | solution 1 for SemigroupBetti.GenData.isSplit_of_mem_fam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:56:00.105098+00:00
-- url     : https://prove2.me/submissions/63f7f278-a077-4336-a39f-ef60a98683bf

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
public import Theorems.Thm_SemigroupBetti_GenData_mem_fam


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {K : Finset (Fin 4)} {d : ℕ} (h : d ∈ G.fam K) : G.IsSplit d K :=
  (G.mem_fam.1 h).2.2.2
end SemigroupBetti.GenData
