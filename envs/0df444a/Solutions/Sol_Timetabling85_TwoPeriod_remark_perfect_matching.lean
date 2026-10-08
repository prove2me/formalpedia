-- Prove2me | solution 1 for Timetabling85.TwoPeriod.remark_perfect_matching
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:42:01.365744+00:00
-- url     : https://prove2.me/submissions/307398d5-1732-4dda-9b19-c0ed2cba9553

import Mathlib

theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (G : SimpleGraph X) (M : G.Subgraph) (hM : M.IsPerfectMatching) :
    (∀ S : Finset X, G.IsIndepSet (S : Set X) → S.card ≤ Fintype.card X / 2) ∧
    (∀ S : Finset X, G.IsIndepSet (S : Set X) → S.card = Fintype.card X / 2 →
      ∀ v w : X, M.Adj v w → (v ∈ S ↔ w ∉ S)) := by
  classical
  have hm := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM
  let mate : X → X := fun v => (hm v).choose
  have ha : ∀ v, M.Adj v (mate v) := fun v => (hm v).choose_spec.1
  have hi : Function.Involutive mate := by
    intro v
    exact hM.1.eq_of_adj_left (ha (mate v)) (ha v).symm
  have hn : Function.Injective mate := hi.injective
  have disj (S : Finset X) (hS : G.IsIndepSet (S : Set X)) :
      Disjoint S (S.image mate) := by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv'
    exact hS hw hv (ha w).ne ((ha w).adj_sub)
  have bound (S : Finset X) (hS : G.IsIndepSet (S : Set X)) :
      S.card + S.card ≤ Fintype.card X := by
    have h := Finset.card_le_card (Finset.subset_univ (S ∪ S.image mate))
    rwa [Finset.card_union_of_disjoint (disj S hS), Finset.card_image_of_injective _ hn,
      Finset.card_univ] at h
  constructor
  · intro S hS
    have := bound S hS
    omega
  · intro S hS hc v w hvw
    have he := hM.even_card
    have hncard : Fintype.card X = S.card + S.card := by
      obtain ⟨k, hk⟩ := he
      omega
    have hu : S ∪ S.image mate = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_union_of_disjoint (disj S hS), Finset.card_image_of_injective _ hn,
        Finset.card_univ, hncard]
    constructor
    · intro hv hw
      exact hS hv hw hvw.ne hvw.adj_sub
    · intro hw
      have hw' : w ∈ S ∪ S.image mate := by rw [hu]; exact Finset.mem_univ _
      have hw'' := (Finset.mem_union.mp hw').resolve_left hw
      obtain ⟨u, hu, hum⟩ := Finset.mem_image.mp hw''
      have huv : u = v := hM.1.eq_of_adj_right (hum ▸ ha u) hvw
      simpa [huv] using hu

#print axioms solution
