-- Prove2me | solution 1 for SemigroupBetti.GenData.sub_mem_of_reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:09:23.560795+00:00
-- url     : https://prove2.me/submissions/e15abcec-7193-42fe-a8ec-eec0d59005e0

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
public import Theorems.Thm_SemigroupBetti_GenData_sub_mem_of_sharesVar
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
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (G : GenData) (K : Type*) [Field K]
namespace SemigroupBetti.GenData
theorem _root_.solution {J : Ideal (MvPolynomial (Fin 4) K)} {d : ℕ}
    (IH : ∀ e < d, ∀ z z' : Fin 4 → ℕ, G.nu z = e → G.nu z' = e → mono K z - mono K z' ∈ J)
    {x y : G.fiber d} (h : (G.nabla d).Reachable x y) : mono K x.1 - mono K y.1 ∈ J := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => simp
  | @cons u v w hadj _ ih =>
    rw [← sub_add_sub_cancel _ (mono K v.1) _]
    exact add_mem (G.sub_mem_of_sharesVar K IH (G.mem_fiber.1 u.2) (G.mem_fiber.1 v.2) hadj.2) ih
end SemigroupBetti.GenData
