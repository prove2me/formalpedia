-- Prove2me | solution 1 for SemigroupBetti.IsPairAntichain.corank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:13:45.588966+00:00
-- url     : https://prove2.me/submissions/fb267c27-cf69-4839-bbd1-1453bc0bbd2a

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
public import Theorems.Thm_SemigroupBetti_IsPairAntichain_snd_inj
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
    {x : ℕ × ℕ} (hx : x ∈ T) : (T.filter (fun y => x.1 ≤ y.1)).card ≤ x.2 := by
  have hle : ∀ y ∈ T, x.1 ≤ y.1 → y.2 ≤ x.2 := by
    intro y hy h1
    by_contra h2
    have := hT x hx y hy h1 (by omega)
    subst this; omega
  have := card_le_card_of_injOn (fun y : ℕ × ℕ => y.2) (s := T.filter (fun y => x.1 ≤ y.1)) (t := Icc 1 x.2)
    (fun y hy => by
      have hy' := mem_filter.1 (mem_coe.1 hy)
      exact mem_coe.2 (mem_Icc.2 ⟨(hpos y hy'.1).2, hle y hy'.1 hy'.2⟩))
    (fun y hy y' hy' h => hT.snd_inj (mem_filter.1 (mem_coe.1 hy)).1
      (mem_filter.1 (mem_coe.1 hy')).1 h)
  simpa using this
end IsPairAntichain
end SemigroupBetti
