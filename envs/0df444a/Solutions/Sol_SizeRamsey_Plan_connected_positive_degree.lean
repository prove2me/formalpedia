-- Prove2me | solution 1 for SizeRamsey.Plan.connected_positive_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:21:19.127473+00:00
-- url     : https://prove2.me/submissions/9dd55adc-45a4-469e-9de9-a1829fd3b752

module
public import Definitions.Def_SizeRamsey_Deletion
public import Definitions.Def_SizeRamsey_Components
public import Theorems.Thm_SizeRamsey_edgeCount_eq_card


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace SizeRamsey.Plan
theorem _root_.solution
    (hc : G.Connected) (hp : 0 < edgeCount G) :
    ∀ v, 0 < G.degree v := by
  intro v
  rw [edgeCount_eq_card, Finset.card_pos] at hp
  obtain ⟨e, he⟩ := hp
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    by_cases hva : v = a
    · exact hva ▸ he.degree_pos_left
    · obtain ⟨p⟩ := hc.preconnected v a
      cases p with
      | nil => exact absurd rfl hva
      | cons h _ => exact h.degree_pos_left
end SizeRamsey.Plan
