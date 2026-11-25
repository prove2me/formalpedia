-- Prove2me | solution 1 for SimpleGraph.choose_le_card_cliqueFinset_add_mul_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:43:12.876285+00:00
-- url     : https://prove2.me/submissions/14746287-79a9-4d38-870d-4d14a070d66e

module
public import Definitions.Def_GoodmanSupersaturation_Goodman
public import Mathlib.Tactic.Rify
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_GoodmanSupersaturation_Supersaturation
public import Theorems.Thm_Finset_choose_le_card_mul_choose
public import Theorems.Thm_SimpleGraph_cliqueCountIn_univ
public import Theorems.Thm_SimpleGraph_degreeWithin_univ
attribute [local simp] SimpleGraph.cliqueCountIn_univ
attribute [local simp] SimpleGraph.degreeWithin_univ



set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*}
namespace SimpleGraph
theorem _root_.solution [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t m : ℕ} (htm : t ≤ m) (hm : m ≤ Fintype.card V)
    (h : ∀ M : Finset V, #M = m →
      (∃ K ⊆ M, G.IsNClique t K) ∨ ∃ K ⊆ M, Gᶜ.IsNClique t K) :
    (Fintype.card V).choose t ≤ (#(G.cliqueFinset t) + #(Gᶜ.cliqueFinset t)) * m.choose t := by
  have hsub : G.cliqueFinset t ∪ Gᶜ.cliqueFinset t ⊆ (univ : Finset V).powersetCard t := by
    intro K hK
    rw [mem_powersetCard]
    rcases mem_union.mp hK with hK | hK <;>
      exact ⟨subset_univ _, (mem_cliqueFinset_iff.mp hK).card_eq⟩
  have := Finset.choose_le_card_mul_choose hsub htm (by simpa using hm) fun M hM => by
    rcases h M (mem_powersetCard.mp hM).2 with ⟨K, hKM, hK⟩ | ⟨K, hKM, hK⟩
    · exact ⟨K, mem_union_left _ (mem_cliqueFinset_iff.mpr hK), hKM⟩
    · exact ⟨K, mem_union_right _ (mem_cliqueFinset_iff.mpr hK), hKM⟩
  rw [card_univ] at this
  exact this.trans (Nat.mul_le_mul_right _ (card_union_le _ _))
end SimpleGraph
