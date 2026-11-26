-- Prove2me | solution 1 for SemigroupBetti.GenData.sel_of_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:13:58.236926+00:00
-- url     : https://prove2.me/submissions/542cb2e1-488c-4692-a336-dfc2523e3aaf

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition
public import Theorems.Thm_SemigroupBetti_GenData_exists_supp_eq_of_split
public import Theorems.Thm_SemigroupBetti_GenData_sel_spec

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} {K : Finset (Fin 4)} (hS : G.IsSplit d K) (hK : K.card = 2) :
    G.nu (G.sel d K) = d ∧ supp (G.sel d K) = K :=
  G.sel_spec (G.exists_supp_eq_of_split hS hK)
end SemigroupBetti.GenData
