-- Prove2me | solution 1 for SimpleGraph.exists_mem_support_adj_not_mem_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:30:00.020786+00:00
-- url     : https://prove2.me/submissions/7cc35942-56a4-4fd9-b196-62ce58a23c51

module
public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_Euler_Basic

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution (hconn : G.Connected) {u v : V} {p : G.Walk u v}
    (hp : p.IsTrail) (hne : ¬ p.IsEulerian) :
    ∃ x ∈ p.support, ∃ y, G.Adj x y ∧ s(x, y) ∉ p.edges := by
  by_contra! h
  apply hne
  -- Todo vértice alcanzable desde el soporte está en el soporte.
  have hclosed : ∀ a b (q : G.Walk a b), a ∈ p.support → b ∈ p.support := by
    intro a b q
    induction q with
    | nil => exact id
    | cons hab q ih =>
      intro ha
      exact ih (p.snd_mem_support_of_mem_edges (h _ ha _ hab))
  have hall : ∀ w, w ∈ p.support := fun w =>
    hclosed u w (hconn.preconnected u w).some p.start_mem_support
  refine hp.isEulerian_of_forall_mem fun e he => ?_
  induction e using Sym2.ind with
  | _ a b => exact h a (hall a) b he
end SimpleGraph
