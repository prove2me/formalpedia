-- Prove2me | solution 1 for SemigroupBetti.GenData.P_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:19:50.949499+00:00
-- url     : https://prove2.me/submissions/00177986-80e2-4cf9-9294-9c86af201ca1

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
public import Theorems.Thm_SemigroupBetti_GenData_card_le_of_coord
public import Theorems.Thm_SemigroupBetti_GenData_isSplit_of_mem_fam
public import Theorems.Thm_SemigroupBetti_GenData_IsSplit_compl
public import Theorems.Thm_SemigroupBetti_GenData_sel_one_bounds
public import Theorems.Thm_SemigroupBetti_GenData_sel_two_bounds


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : G.P ≤ G.R - 1 := by
  have hc : ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by decide
  have h1 : G.P ≤ G.B - 1 :=
    G.card_le_of_coord (i := 0) (k := 1) (by decide) rfl G.famP
      (fun d hd => G.isSplit_of_mem_fam hd)
      (fun d hd => G.sel_one_bounds (G.isSplit_of_mem_fam hd) (by decide) (by decide))
  have h2 : G.P ≤ G.W - G.A - 1 :=
    G.card_le_of_coord (K := {2, 3}) (i := 3) (k := 2) (by decide) (by decide) G.famP
      (fun d hd => hc ▸ (G.isSplit_of_mem_fam hd).compl)
      (fun d hd => G.sel_two_bounds (hc ▸ (G.isSplit_of_mem_fam hd).compl) (by decide)
        (by decide))
  unfold R; omega
end SemigroupBetti.GenData
