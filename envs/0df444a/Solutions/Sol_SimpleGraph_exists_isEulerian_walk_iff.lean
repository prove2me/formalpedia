-- Prove2me | solution 1 for SimpleGraph.exists_isEulerian_walk_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:09:44.897733+00:00
-- url     : https://prove2.me/submissions/d3344399-8ea9-456d-bd9c-20ea39f2144e

module
public import Definitions.Def_Euler_Basic
public import Definitions.Def_Euler_Trail
public import Theorems.Thm_SimpleGraph_exists_isEulerian_of_parity
public import Theorems.Thm_SimpleGraph_exists_isEulerian_circuit_at

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution (hconn : G.Connected) :
    (∃ u v, ∃ p : G.Walk u v, p.IsEulerian) ↔
      Fintype.card {v | Odd (G.degree v)} = 0 ∨ Fintype.card {v | Odd (G.degree v)} = 2 := by
  constructor
  · rintro ⟨u, v, p, hp⟩
    exact hp.card_odd_degree
  · intro hcard
    rw [← Set.toFinset_card, Set.toFinset_ofPred] at hcard
    rcases hcard with h0 | h2
    · obtain ⟨a⟩ := hconn.nonempty
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
      exact ⟨a, a, exists_isEulerian_circuit_at hconn
        (fun x => Nat.not_odd_iff_even.mp (h0 (Finset.mem_univ x))) a⟩
    · obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp h2
      refine ⟨a, b, exists_isEulerian_of_parity hconn fun x => ?_⟩
      have hx := Finset.ext_iff.mp hs x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton] at hx
      rw [← Nat.not_odd_iff_even, hx]
      simp [hab, not_or]
end SimpleGraph
