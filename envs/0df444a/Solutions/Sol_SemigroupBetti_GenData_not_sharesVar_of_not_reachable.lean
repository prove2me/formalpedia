-- Prove2me | solution 1 for SemigroupBetti.GenData.not_sharesVar_of_not_reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:34:26.789087+00:00
-- url     : https://prove2.me/submissions/f01dc2eb-2c31-423b-a7e8-8d66991df706

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber
public import Theorems.Thm_SemigroupBetti_GenData_reachable_of_sharesVar

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} {z y : G.fiber d}
    (h : ¬ (G.nabla d).Reachable z y) : ¬ SharesVar z.1 y.1 :=
  fun hs => h (G.reachable_of_sharesVar hs)
end SemigroupBetti.GenData
