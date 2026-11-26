-- Prove2me | solution 1 for SemigroupBetti.IsPairAntichain.rank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:12:24.772495+00:00
-- url     : https://prove2.me/submissions/e37b68b9-3f75-44c8-944f-9dc7d8a4f306

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
public import Theorems.Thm_SemigroupBetti_IsPairAntichain_fst_inj
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_mem_supp
attribute [local simp] SemigroupBetti.GenData.mem_fiber
attribute [local simp] SemigroupBetti.GenData.n_one
attribute [local simp] SemigroupBetti.GenData.n_three
attribute [local simp] SemigroupBetti.GenData.n_two
attribute [local simp] SemigroupBetti.GenData.n_zero
attribute [local simp] SemigroupBetti.GenData.nu_zero
attribute [local simp] SemigroupBetti.mem_supp



set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
variable {T : Finset (ℕ × ℕ)}
namespace SemigroupBetti
namespace IsPairAntichain
theorem _root_.solution (hT : IsPairAntichain T) (hpos : ∀ x ∈ T, 1 ≤ x.1 ∧ 1 ≤ x.2)
    {x : ℕ × ℕ} : (T.filter (fun y => y.1 ≤ x.1)).card ≤ x.1 := by
  have := card_le_card_of_injOn (fun y : ℕ × ℕ => y.1) (s := T.filter (fun y => y.1 ≤ x.1)) (t := Icc 1 x.1)
    (fun y hy => by
      have hy' := mem_filter.1 (mem_coe.1 hy)
      exact mem_coe.2 (mem_Icc.2 ⟨(hpos y hy'.1).1, hy'.2⟩))
    (fun y hy y' hy' h => hT.fst_inj (mem_filter.1 (mem_coe.1 hy)).1
      (mem_filter.1 (mem_coe.1 hy')).1 h)
  simpa using this
end IsPairAntichain
end SemigroupBetti
