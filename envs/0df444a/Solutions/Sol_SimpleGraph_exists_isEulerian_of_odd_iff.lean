-- Prove2me | solution 1 for SimpleGraph.exists_isEulerian_of_odd_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:04:45.797586+00:00
-- url     : https://prove2.me/submissions/84caabb1-343a-4762-bf7f-f3e0dfe7c54b

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
theorem _root_.solution (hconn : G.Connected) {a b : V} (hab : a ≠ b)
    (hodd : ∀ x, Odd (G.degree x) ↔ x = a ∨ x = b) : ∃ p : G.Walk a b, p.IsEulerian :=
  exists_isEulerian_of_parity hconn fun x => by
    rw [← Nat.not_odd_iff_even, hodd]
    simp [hab, not_or]
end SimpleGraph
