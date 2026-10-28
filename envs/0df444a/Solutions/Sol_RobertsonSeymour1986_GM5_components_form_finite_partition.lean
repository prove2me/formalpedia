-- Prove2me | solution 1 for RobertsonSeymour1986.GM5.components_form_finite_partition
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T21:28:34.1121+00:00
-- url     : https://prove2.me/submissions/5745c8d4-60c1-4f8c-81c6-fb9be036ac66

import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : ℕ)
    (hcomp : ∀ v : V,
      RobertsonSeymour1986.GM5.TreewidthLE
        (G.induce {u : V | G.Reachable u v}) w) :
    ∃ (ι : Type) (_ : Fintype ι) (C : ι → Finset V),
      (∀ v : V, ∃ i, v ∈ C i) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      (∀ x y : V, G.Adj x y → ∃ i, x ∈ C i ∧ y ∈ C i) ∧
      (∀ i, RobertsonSeymour1986.GM5.TreewidthLE
        (G.induce {u : V | u ∈ C i}) w) := by
  classical
  let C : G.ConnectedComponent → Finset V :=
    fun i => Finset.univ.filter (fun u => G.connectedComponentMk u = i)
  refine ⟨G.ConnectedComponent, inferInstance, C, ?_, ?_, ?_, ?_⟩
  · intro v
    exact ⟨G.connectedComponentMk v, by simp [C]⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    apply hij
    have hxi' : G.connectedComponentMk x = i := by
      simpa [C] using hxi
    have hxj' : G.connectedComponentMk x = j := by
      simpa [C] using hxj
    exact hxi'.symm.trans hxj'
  · intro x y hadj
    refine ⟨G.connectedComponentMk x, ?_, ?_⟩
    · simp [C]
    · have hxy : G.connectedComponentMk x = G.connectedComponentMk y :=
        SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
      simp [C, hxy]
  · intro i
    rcases i.exists_rep with ⟨v, hv⟩
    have hset :
        {u : V | u ∈ C i} = {u : V | G.Reachable u v} := by
      ext u
      simp only [Set.mem_setOf_eq, C, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [← hv]
      exact SimpleGraph.ConnectedComponent.eq
    rw [hset]
    exact hcomp v