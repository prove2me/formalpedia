-- Prove2me | solution 1 for SemigroupBetti.GenData.nu_rep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:07:02.393358+00:00
-- url     : https://prove2.me/submissions/60f603d2-76ee-4df3-845b-d5ae8620a2bb

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
attribute [local simp] SemigroupBetti.GenData.mem_fiber



set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (G : GenData) (K : Type*) [Field K]
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} (C : (G.nabla d).ConnectedComponent) : G.nu (G.rep C) = d :=
  G.mem_fiber.1 (Quot.out C).2
end SemigroupBetti.GenData
