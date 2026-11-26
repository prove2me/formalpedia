-- Prove2me | solution 1 for SemigroupBetti.GenData.beta1_eq_sum_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:15:39.668799+00:00
-- url     : https://prove2.me/submissions/76bdef51-bd6d-4c86-a195-6add3c1091d0

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_ncomp_le_one_of_H_lt
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_mem_supp
attribute [local simp] SemigroupBetti.GenData.n_one
attribute [local simp] SemigroupBetti.GenData.n_three
attribute [local simp] SemigroupBetti.GenData.n_two
attribute [local simp] SemigroupBetti.GenData.n_zero
attribute [local simp] SemigroupBetti.GenData.nu_zero
attribute [local simp] SemigroupBetti.mem_supp


attribute [local simp] SemigroupBetti.GenData.mem_fiber

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {K : ℕ} (hK : G.H ≤ K) :
    G.beta1 = ∑ d ∈ range (K + 1), (G.ncomp d - 1) := by
  unfold beta1
  rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : G.H + 1 ≤ K + 1))]
  intro d hd hd'
  simp only [mem_range] at hd hd'
  have := G.ncomp_le_one_of_H_lt (d := d) (by omega)
  omega
end SemigroupBetti.GenData
