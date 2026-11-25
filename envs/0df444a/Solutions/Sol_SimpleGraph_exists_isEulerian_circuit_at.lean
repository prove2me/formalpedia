-- Prove2me | solution 1 for SimpleGraph.exists_isEulerian_circuit_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:04:44.7418+00:00
-- url     : https://prove2.me/submissions/b1858517-1f7d-4169-99b9-b8cf54b26420

module
public import Definitions.Def_Euler_Basic
public import Definitions.Def_Euler_Trail
public import Theorems.Thm_SimpleGraph_exists_isEulerian_of_parity

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution (hconn : G.Connected) (heven : ∀ v, Even (G.degree v))
    (a : V) : ∃ p : G.Walk a a, p.IsEulerian :=
  exists_isEulerian_of_parity hconn fun x => iff_of_true (heven x) fun h => absurd rfl h
end SimpleGraph
