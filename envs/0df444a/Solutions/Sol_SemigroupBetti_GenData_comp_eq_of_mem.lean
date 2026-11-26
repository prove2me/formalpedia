-- Prove2me | solution 1 for SemigroupBetti.GenData.comp_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:09:31.962823+00:00
-- url     : https://prove2.me/submissions/9e5bf06b-a326-413e-b23c-6d8d7abed313

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition
public import Theorems.Thm_SemigroupBetti_GenData_compSupp_disjoint
public import Theorems.Thm_SemigroupBetti_GenData_supp_subset_compSupp
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
theorem _root_.solution {d : ℕ} {C : (G.nabla d).ConnectedComponent} (z : G.fiber d) {i : Fin 4}
    (hi : i ∈ G.compSupp C) (hzi : 0 < z.1 i) : (G.nabla d).connectedComponentMk z = C := by
  by_contra hne
  exact Finset.disjoint_left.1 (G.compSupp_disjoint hne) (G.supp_subset_compSupp z
    (mem_supp.2 hzi)) hi
end SemigroupBetti.GenData
