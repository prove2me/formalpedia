-- Prove2me | solution 1 for WilliamsonShmoys.componentPartition_of_disconnected__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:40:34.917179+00:00
-- url     : https://prove2.me/submissions/c9507f6d-b98c-4b56-aedc-278f9caf7d18

import Mathlib

set_option autoImplicit false
theorem WilliamsonShmoys.componentPartition_of_disconnected__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hconn : ¬ L.Connected)
    (hn : 3 ≤ Fintype.card V) :
    letI : DecidableRel L.Adj := dL
    ∃ C : Finset (Finset V),
      2 ≤ C.card ∧
      (∀ s ∈ C, s.Nonempty) ∧
      (∀ v : V, ∃ s ∈ C, v ∈ s) ∧
      (∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t) ∧
      (∑ s ∈ C, s.card) = Fintype.card V ∧
      (∀ s ∈ C, (L.induce (↑s : Set V)).Connected) := by
  letI : DecidableRel L.Adj := dL
  classical
  let f : L.ConnectedComponent → Finset V := fun c => Finset.univ.filter (fun v => L.connectedComponentMk v = c)
  have hf : ∀ c, (↑(f c) : Set V) = c.supp := by
    intro c; ext v; simp [f, SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hfinj : Function.Injective f := by
    intro c d h
    have : c.supp = d.supp := by rw [← hf, ← hf, h]
    exact SimpleGraph.ConnectedComponent.supp_inj.mp this
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  refine ⟨Finset.univ.image f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ]
    by_contra hlt
    push_neg at hlt
    apply hconn
    haveI : Subsingleton L.ConnectedComponent := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    refine ⟨fun u v => ?_⟩
    exact SimpleGraph.ConnectedComponent.exact (Subsingleton.elim _ _)
  · intro s hs
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hs
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ v => exact ⟨v, by simp [f]⟩
  · intro v
    exact ⟨f (L.connectedComponentMk v), Finset.mem_image_of_mem _ (Finset.mem_univ _), by simp [f]⟩
  · intro s hs t ht hst
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp ht
    have hcd : c ≠ d := fun h => hst (h ▸ rfl)
    rw [← Finset.disjoint_coe, hf, hf]
    exact L.pairwise_disjoint_supp_connectedComponent hcd
  · rw [Finset.sum_image (fun x _ y _ h => hfinj h)]
    rw [Finset.card_univ.symm.trans rfl]
    exact (Finset.card_eq_sum_card_fiberwise (f := fun v => L.connectedComponentMk v)
      (fun v _ => Finset.mem_univ _)).symm
  · intro s hs
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hs
    rw [hf]
    exact (SimpleGraph.ConnectedComponent.maximal_connected_induce_supp c).1

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hconn : ¬ L.Connected)
    (hn : 3 ≤ Fintype.card V) :
    letI : DecidableRel L.Adj := dL
    ∃ C : Finset (Finset V),
      2 ≤ C.card ∧
      (∀ s ∈ C, s.Nonempty) ∧
      (∀ v : V, ∃ s ∈ C, v ∈ s) ∧
      (∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t) ∧
      (∑ s ∈ C, s.card) = Fintype.card V ∧
      (∀ s ∈ C, (L.induce (↑s : Set V)).Connected) :=
  WilliamsonShmoys.componentPartition_of_disconnected__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a1 L dL hconn hn
