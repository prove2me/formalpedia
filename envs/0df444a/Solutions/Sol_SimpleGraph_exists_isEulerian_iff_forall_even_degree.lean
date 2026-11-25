-- Prove2me | solution 1 for SimpleGraph.exists_isEulerian_iff_forall_even_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:48:56.874279+00:00
-- url     : https://prove2.me/submissions/0ca4f6b3-9936-43cf-b40d-2aa177c7bf23

module
public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_Euler_Basic
public import Theorems.Thm_SimpleGraph_exists_isEulerian_of_forall_even_degree

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution (hconn : G.Connected) :
    (∃ u, ∃ p : G.Walk u u, p.IsEulerian) ↔ ∀ v, Even (G.degree v) := by
  constructor
  · rintro ⟨u, p, hp⟩ v
    exact hp.even_degree_iff.mpr fun h => absurd rfl h
  · exact exists_isEulerian_of_forall_even_degree hconn
end SimpleGraph
