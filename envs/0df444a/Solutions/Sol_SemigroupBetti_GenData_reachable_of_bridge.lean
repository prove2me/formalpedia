-- Prove2me | solution 1 for SemigroupBetti.GenData.reachable_of_bridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:51:57.999798+00:00
-- url     : https://prove2.me/submissions/4ef12150-5c32-4f0f-8018-8dea4283bf05

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_reachable_of_sharesVar
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_SharesVar_symm
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
theorem _root_.solution {d : ℕ} {z y : G.fiber d} (b : Fin 4 → ℕ) (hb : G.nu b = d)
    (hz : SharesVar b z.1) (hy : SharesVar b y.1) : (G.nabla d).Reachable z y := by
  let b' : G.fiber d := ⟨b, G.mem_fiber.2 hb⟩
  exact (G.reachable_of_sharesVar (z := b') hz).symm.trans (G.reachable_of_sharesVar hy)
end SemigroupBetti.GenData
