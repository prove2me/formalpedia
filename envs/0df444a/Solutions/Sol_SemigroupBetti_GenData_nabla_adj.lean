-- Prove2me | solution 1 for SemigroupBetti.GenData.nabla_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:33:55.88497+00:00
-- url     : https://prove2.me/submissions/0c619739-7fe9-4ab7-ad94-615b14a31761

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
theorem _root_.solution {d : ℕ} {z z' : G.fiber d} :
    (G.nabla d).Adj z z' ↔ z ≠ z' ∧ SharesVar z.1 z'.1 := Iff.rfl
end SemigroupBetti.GenData
