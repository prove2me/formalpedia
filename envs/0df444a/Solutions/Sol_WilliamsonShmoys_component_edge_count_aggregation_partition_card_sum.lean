-- Prove2me | solution 1 for WilliamsonShmoys.component_edge_count_aggregation_partition_card_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:03:41.773617+00:00
-- url     : https://prove2.me/submissions/ec83bea9-f0e9-4e73-9dad-d3dca4fe1e9a

import Mathlib

set_option autoImplicit false

theorem solution
    (V : Type) [Fintype V]
    (C : Finset (Finset V))
    (hPartition : (∀ S ∈ C, S.Nonempty) ∧
      ∀ v : V, ∃! S : Finset V, S ∈ C ∧ v ∈ S) :
    C.sum Finset.card = Fintype.card V := by
  classical
  let I : Type := {S : Finset V // S ∈ C}
  let E : Type := Σ S : I, {v : V // v ∈ S.1}
  let f : E → V := fun x => x.2.1
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      rcases a with ⟨s, x⟩
      rcases b with ⟨t, y⟩
      change x.1 = y.1 at hab
      obtain ⟨S, hS, hUnique⟩ := hPartition.2 x.1
      have hs : s.1 ∈ C ∧ x.1 ∈ s.1 := ⟨s.2, x.2⟩
      have ht : t.1 ∈ C ∧ x.1 ∈ t.1 :=
        ⟨t.2, by simpa [hab] using y.2⟩
      have hs_eq : s.1 = S := hUnique s.1 hs
      have ht_eq : t.1 = S := hUnique t.1 ht
      have hst : s = t := Subtype.ext (hs_eq.trans ht_eq.symm)
      subst t
      exact congrArg (fun z : {v : V // v ∈ s.1} => (⟨s, z⟩ : E))
        (Subtype.ext hab)
    · intro v
      obtain ⟨S, hS, hUnique⟩ := hPartition.2 v
      exact ⟨⟨⟨S, hS.1⟩, ⟨v, hS.2⟩⟩, rfl⟩
  have hcard : Fintype.card E = Fintype.card V :=
    Fintype.card_congr (Equiv.ofBijective f hf)
  calc
    C.sum Finset.card = ∑ S : I, Fintype.card {v : V // v ∈ S.1} := by
      simp [I, Finset.sum_attach]
    _ = Fintype.card E := by simp [E]
    _ = Fintype.card V := hcard