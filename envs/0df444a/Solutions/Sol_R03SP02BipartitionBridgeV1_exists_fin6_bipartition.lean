-- Prove2me | solution 1 for R03SP02BipartitionBridgeV1.exists_fin6_bipartition
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:55:02.513921+00:00
-- url     : https://prove2.me/submissions/8ad89fdd-dd83-4adf-b4e6-2048597d24ec

import Definitions.Def_cubic_p3_partition_models

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace R03SP02BipartitionBridgeV1

open CubicP3Partition
open scoped BigOperators

noncomputable section

variable {V : Type} [Fintype V]

lemma cubic_to_math_degree (G : SimpleGraph V) (hC : Cubic G)
    [DecidableRel G.Adj] : ∀ v, G.degree v = 3 := by
  intro v
  have hv := hC v
  unfold CubicP3Partition.degree at hv
  rw [Nat.card_eq_fintype_card] at hv
  change Finset.card (G.neighborFinset v) = 3
  rw [SimpleGraph.neighborFinset_def, Set.toFinset_card]
  exact hv


end
end R03SP02BipartitionBridgeV1

open R03SP02BipartitionBridgeV1
open CubicP3Partition
open scoped BigOperators
variable {V : Type} [Fintype V]
theorem solution
    (G : SimpleGraph V) (hC : Cubic G) (hB : G.IsBipartite)
    (hcard : Fintype.card V = 12) :
    ∃ s t : Set V, G.IsBipartiteWith s t ∧
      ∃ e : (Fin 6 ⊕ Fin 6) ≃ V,
        (∀ a, e (Sum.inl a) ∈ s) ∧ (∀ b, e (Sum.inr b) ∈ t) := by
  classical
  obtain ⟨s, t, hst⟩ := hB.exists_isBipartiteWith
  let S : Finset V := Finset.univ.filter (fun v => v ∈ s)
  let T : Finset V := Finset.univ.filter (fun v => v ∈ t)
  have hST : G.IsBipartiteWith (S : Set V) (T : Set V) := by
    simpa [S, T] using hst
  have hdeg : ∀ v, G.degree v = 3 := cubic_to_math_degree G hC
  have hadj : ∀ v : V, ∃ w : V, G.Adj v w := by
    intro v
    have hpos : 0 < Nat.card {w : V // G.Adj v w} := by
      have hc := hC v
      unfold CubicP3Partition.degree at hc
      rw [hc]
      decide
    obtain ⟨w⟩ := (Nat.card_pos_iff.mp hpos).1
    exact ⟨w.1, w.2⟩
  have hcover : S ∪ T = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    obtain ⟨w, hw⟩ := hadj v
    rcases hst.mem_of_adj hw with ⟨hs, _⟩ | ⟨ht, _⟩
    · apply Finset.mem_union_left
      simp [S, hs]
    · apply Finset.mem_union_right
      simp [T, ht]
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro v hvS hvT
    exact Set.disjoint_left.mp hst.disjoint (by simpa [S] using hvS) (by simpa [T] using hvT)
  have hsum : ∑ v ∈ S, G.degree v = ∑ v ∈ T, G.degree v := by
    exact SimpleGraph.isBipartiteWith_sum_degrees_eq hST
  have hcardST : S.card = T.card := by
    simpa [hdeg] using hsum
  have htotal : S.card + T.card = 12 := by
    calc
      S.card + T.card = (S ∪ T).card :=
        (Finset.card_union_of_disjoint hdisj).symm
      _ = Finset.univ.card := by rw [hcover]
      _ = Fintype.card V := Finset.card_univ
      _ = 12 := hcard
  have hS6 : S.card = 6 := by omega
  have hT6 : T.card = 6 := by omega
  let eS : Fin 6 ≃ S := Fintype.equivOfCardEq (by simp [hS6])
  let eT : Fin 6 ≃ T := Fintype.equivOfCardEq (by simp [hT6])
  let f : S ⊕ T → V := Sum.elim Subtype.val Subtype.val
  have hf_inj : Function.Injective f := by
    intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        simp only [f, Sum.elim_inl] at hxy
        exact congrArg Sum.inl (Subtype.ext hxy)
      | inr y =>
        have hval : (x : V) = (y : V) := by simpa [f] using hxy
        have hnot : (x : V) ∉ T := Finset.disjoint_left.mp hdisj x.2
        exact (hnot (hval ▸ y.2)).elim
    | inr x =>
      cases y with
      | inl y =>
        have hval : (x : V) = (y : V) := by simpa [f] using hxy
        have hnot : (x : V) ∉ T := Finset.disjoint_left.mp hdisj (hval ▸ y.2)
        exact (hnot x.2).elim
      | inr y =>
        simp only [f, Sum.elim_inr] at hxy
        exact congrArg Sum.inr (Subtype.ext hxy)
  have hf_surj : Function.Surjective f := by
    intro v
    have hv : v ∈ S ∪ T := by rw [hcover]; simp
    rcases Finset.mem_union.mp hv with hvS | hvT
    · exact ⟨Sum.inl ⟨v, hvS⟩, rfl⟩
    · exact ⟨Sum.inr ⟨v, hvT⟩, rfl⟩
  have hSset : (S : Set V) = s := by
    ext v
    simp [S]
  have hTset : (T : Set V) = t := by
    ext v
    simp [T]
  let eST : S ⊕ T ≃ V := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have heST_coe : ⇑eST = f := by
    dsimp [eST]
    exact Equiv.coe_ofBijective f ⟨hf_inj, hf_surj⟩
  let e : (Fin 6 ⊕ Fin 6) ≃ V := (Equiv.sumCongr eS eT).trans eST
  refine ⟨s, t, hst, e, ?_, ?_⟩
  · intro a
    simp only [e, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl]
    rw [congrFun heST_coe (Sum.inl (eS a))]
    simp only [f, Sum.elim_inl]
    rw [← hSset]
    exact (eS a).property
  · intro b
    simp only [e, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr]
    rw [congrFun heST_coe (Sum.inr (eT b))]
    simp only [f, Sum.elim_inr]
    rw [← hTset]
    exact (eT b).property

