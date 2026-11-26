-- Prove2me | solution 1 for SemigroupBetti.GenData.comp_eq_of_replace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:15:14.214963+00:00
-- url     : https://prove2.me/submissions/9611a5b4-18af-4987-901e-0ff284bd274b

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber
public import Theorems.Thm_SemigroupBetti_GenData_nu_replace
public import Theorems.Thm_SemigroupBetti_GenData_reachable_of_bridge

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} {u v x : Fin 4 → ℕ} (hux : u ≤ x) (huv : G.nu u = G.nu v)
    (hx : G.nu x = d) {z y : G.fiber d} (hz : SharesVar (x - u + v) z.1)
    (hy : SharesVar (x - u + v) y.1) :
    (G.nabla d).connectedComponentMk z = (G.nabla d).connectedComponentMk y :=
  SimpleGraph.ConnectedComponent.sound
    (G.reachable_of_bridge _ ((G.nu_replace hux huv).trans hx) hz hy)
end SemigroupBetti.GenData
