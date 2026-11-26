-- Prove2me | solution 1 for SemigroupBetti.GenData.n_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:27:38.358901+00:00
-- url     : https://prove2.me/submissions/3962bf5b-d432-4b08-bef8-edf5e1fb0343

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_mem_supp
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_three
attribute [local simp] SemigroupBetti.mem_supp
attribute [local simp] SemigroupBetti.GenData.n_zero
attribute [local simp] SemigroupBetti.GenData.n_one
attribute [local simp] SemigroupBetti.GenData.n_two
attribute [local simp] SemigroupBetti.GenData.n_three

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : StrictMono G.n := by
  have h1 := G.a_pos; have h2 := G.a_lt_b; have h3 := G.b_lt_w
  refine Fin.strictMono_iff_lt_succ.2 ?_
  intro i; fin_cases i <;> simp <;> omega
end SemigroupBetti.GenData
