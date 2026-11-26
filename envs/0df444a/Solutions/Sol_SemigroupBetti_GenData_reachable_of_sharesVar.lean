-- Prove2me | solution 1 for SemigroupBetti.GenData.reachable_of_sharesVar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:30:18.998297+00:00
-- url     : https://prove2.me/submissions/e4a4d6e6-d82c-477f-b6e5-d653af49dea8

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} {z y : G.fiber d} (h : SharesVar z.1 y.1) :
    (G.nabla d).Reachable z y := by
  by_cases hzy : z = y
  · subst hzy; rfl
  · exact SimpleGraph.Adj.reachable ⟨hzy, h⟩
end SemigroupBetti.GenData
