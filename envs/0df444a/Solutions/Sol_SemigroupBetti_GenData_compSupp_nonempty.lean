-- Prove2me | solution 1 for SemigroupBetti.GenData.compSupp_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:58:55.097043+00:00
-- url     : https://prove2.me/submissions/7cf4b289-a0e4-40db-9f80-4eca1a30d550

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_mem_compSupp
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
theorem _root_.solution {d : ℕ} (hd : 0 < d) (C : (G.nabla d).ConnectedComponent) :
    (G.compSupp C).Nonempty := by
  induction C using SimpleGraph.ConnectedComponent.ind with
  | h z =>
    have hz0 : z.1 ≠ 0 := by
      intro h0; have := (G.mem_fiber.1 z.2); rw [h0, nu_zero] at this; omega
    obtain ⟨i, hi⟩ : ∃ i, z.1 i ≠ 0 := by
      by_contra hc; push Not at hc; exact hz0 (funext hc)
    exact ⟨i, G.mem_compSupp.2 ⟨z, rfl, Nat.pos_of_ne_zero hi⟩⟩
end SemigroupBetti.GenData
