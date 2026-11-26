-- Prove2me | solution 1 for SemigroupBetti.GenData.nu_replace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:30:31.331623+00:00
-- url     : https://prove2.me/submissions/fa6e19db-e6d4-46bb-80cd-d9be840c8ec4

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber
public import Theorems.Thm_SemigroupBetti_GenData_nu_add
public import Theorems.Thm_SemigroupBetti_GenData_nu_sub


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {u v x : Fin 4 → ℕ} (hux : u ≤ x) (huv : G.nu u = G.nu v) :
    G.nu (x - u + v) = G.nu x := by
  rw [G.nu_add, G.nu_sub hux, huv, add_comm]
end SemigroupBetti.GenData
