-- Prove2me | solution 1 for SnarkGen.CycleCover.cycle_cover_four_thirds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T19:33:31.208411+00:00
-- url     : https://prove2.me/submissions/6b73b899-1524-4f89-83dc-7efccc8e8dd3

import Mathlib
import Definitions.Def_SnarkGen_EdgeInsertion_Colourable
import Definitions.Def_SnarkGen_CycleCover_IsCycleCover

set_option autoImplicit false

open SnarkGen.CycleCover SimpleGraph in
theorem cover_of_isCycles {V : Type*} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
    (hle : H ≤ G) (hH : H.IsCycles) :
    ∃ F : Finset (Finset (Sym2 V)), (∀ C ∈ F, IsCycleEdges G C) ∧
      (∀ e ∈ H.edgeSet, ∃ C ∈ F, e ∈ C) ∧ coverLength F ≤ H.edgeSet.ncard := by
  classical
  let comp : H.ConnectedComponent → Finset (Sym2 V) := fun c =>
    Finset.univ.filter (fun e : Sym2 V => e ∈ H.edgeSet ∧ ∀ v ∈ e, H.connectedComponentMk v = c)
  have hmem : ∀ c e, e ∈ comp c ↔ e ∈ H.edgeSet ∧ ∀ v ∈ e, H.connectedComponentMk v = c := by
    intro c e; simp [comp]
  have hdisj : ∀ c c', c ≠ c' → Disjoint (comp c) (comp c') := by
    intro c c' hne
    rw [Finset.disjoint_left]
    intro e he he'
    rw [hmem] at he he'
    induction e using Sym2.ind with
    | h a b =>
      exact hne ((he.2 a (by simp)).symm.trans (he'.2 a (by simp)))
  have hsub : ∀ c, (comp c : Set (Sym2 V)) ⊆ H.edgeSet := by
    intro c e he; exact ((hmem c e).1 he).1
  refine ⟨(Finset.univ.image comp).filter (fun C => C.Nonempty), ?_, ?_, ?_⟩
  · intro C hC
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hC
    obtain ⟨⟨c, rfl⟩, e, he⟩ := hC
    rw [hmem] at he
    induction e using Sym2.ind with
    | h a b =>
      have hab : H.Adj a b := he.1
      have hac : H.connectedComponentMk a = c := he.2 a (by simp)
      obtain ⟨p, hp, hpv⟩ := hH.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
        (c := c) (v := a) (by rw [← hac]; simp) ⟨b, hab⟩
      refine ⟨a, p.mapLe hle, hp.mapLe hle, ?_⟩
      ext e
      rw [List.mem_toFinset, Walk.edges_mapLe_eq_edges, hmem]
      induction e using Sym2.ind with
      | h x y =>
        constructor
        · intro hxy
          refine ⟨p.edges_subset_edgeSet hxy, ?_⟩
          intro v hv
          have hvs : v ∈ p.support := by
            rcases Sym2.mem_iff.1 hv with rfl | rfl
            · exact p.fst_mem_support_of_mem_edges hxy
            · exact p.snd_mem_support_of_mem_edges hxy
          have : v ∈ c.supp := by
            rw [← hpv, Walk.mem_verts_toSubgraph]; exact hvs
          exact this
        · rintro ⟨hxy, hv⟩
          have hx : x ∈ p.toSubgraph.verts := by
            rw [hpv]; exact hv x (by simp)
          have hadj : H.Adj x y := hxy
          have := (hp.adj_toSubgraph_iff_of_isCycles hH hx y).2 hadj
          exact p.mem_edges_toSubgraph.1 this
  · intro e he
    induction e using Sym2.ind with
    | h a b =>
      have hab : H.Adj a b := he
      have hba : H.connectedComponentMk b = H.connectedComponentMk a :=
        (SimpleGraph.ConnectedComponent.eq.2 hab.reachable).symm
      refine ⟨comp (H.connectedComponentMk a), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
        refine ⟨⟨_, rfl⟩, s(a, b), ?_⟩
        rw [hmem]
        refine ⟨he, ?_⟩
        intro v hv
        rcases Sym2.mem_iff.1 hv with rfl | rfl
        · rfl
        · exact hba
      · rw [hmem]
        refine ⟨he, ?_⟩
        intro v hv
        rcases Sym2.mem_iff.1 hv with rfl | rfl
        · rfl
        · exact hba
  · calc coverLength ((Finset.univ.image comp).filter (fun C => C.Nonempty))
        ≤ ∑ C ∈ Finset.univ.image comp, C.card := by
          unfold coverLength
          exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ ≤ ∑ c : H.ConnectedComponent, (comp c).card :=
          Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
      _ = (Finset.univ.biUnion comp).card := by
          rw [Finset.card_biUnion]
          intro c _ c' _ hne
          exact hdisj c c' hne
      _ ≤ H.edgeSet.ncard := by
          rw [← Set.ncard_coe_finset]
          apply Set.ncard_le_ncard _ (Set.toFinite _)
          intro e he
          simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_iUnion, Set.mem_univ,
            Finset.mem_coe, exists_true_left] at he
          obtain ⟨c, hc⟩ := he
          exact hsub c (Finset.mem_coe.2 hc)

def Hg {V : Type*} (G : SimpleGraph V) (col : Sym2 V → Fin 3) (j : Fin 3) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ col s(a, b) ≠ j
  symm := ⟨fun a b h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩

theorem Hg_le {V : Type*} (G : SimpleGraph V) (col : Sym2 V → Fin 3) (j : Fin 3) :
    Hg G col j ≤ G := fun _ _ h => h.1

theorem Hg_isCycles {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcubic : G.IsRegularOfDegree 3) (col : Sym2 V → Fin 3)
    (hcol : ∀ v w w', G.Adj v w → G.Adj v w' → w ≠ w' → col s(v, w) ≠ col s(v, w'))
    (j : Fin 3) : (Hg G col j).IsCycles := by
  classical
  intro v _
  have hN : (G.neighborFinset v).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hcubic v
  have hinj : Set.InjOn (fun w => col s(v, w)) (G.neighborFinset v : Set V) := by
    intro w hw w' hw' h
    by_contra hne
    exact hcol v w w' (by simpa using hw) (by simpa using hw') hne h
  have himg : (G.neighborFinset v).image (fun w => col s(v, w)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, hN]; simp
  have hset : (Hg G col j).neighborSet v =
      ↑((G.neighborFinset v).filter (fun w => col s(v, w) ≠ j)) := by
    ext w
    simp [Hg]
  rw [hset, Set.ncard_coe_finset]
  have : ((G.neighborFinset v).filter (fun w => col s(v, w) ≠ j)).image (fun w => col s(v, w))
      = Finset.univ.erase j := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨w, ⟨_, h⟩, rfl⟩; exact h
    · intro hx
      have : x ∈ (G.neighborFinset v).image (fun w => col s(v, w)) := by rw [himg]; simp
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 this
      exact ⟨w, ⟨hw, hx⟩, rfl⟩
  rw [← Finset.card_image_of_injOn (f := fun w => col s(v, w)), this]
  · simp
  · exact hinj.mono (by intro w hw; exact Finset.mem_filter.1 hw |>.1)

open SnarkGen.CycleCover in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcubic : G.IsRegularOfDegree 3) (hcol : SnarkGen.EdgeInsertion.Colourable G) :
    ∃ F : Finset (Finset (Sym2 V)), IsCycleCover G F ∧
      3 * coverLength F ≤ 4 * G.edgeFinset.card := by
  classical
  obtain ⟨C⟩ := hcol
  let col : Sym2 V → Fin 3 := fun e => if h : e ∈ G.edgeSet then C ⟨e, h⟩ else 0
  have hcolv : ∀ v w w', G.Adj v w → G.Adj v w' → w ≠ w' → col s(v, w) ≠ col s(v, w') := by
    intro v w w' h1 h2 hne
    have e1 : s(v, w) ∈ G.edgeSet := h1
    have e2 : s(v, w') ∈ G.edgeSet := h2
    simp only [col, dif_pos e1, dif_pos e2]
    apply C.valid
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    refine ⟨?_, v, by simp, by simp⟩
    intro h
    apply hne
    have := congrArg Subtype.val h
    exact Sym2.congr_right.1 this
  have hEj : ∀ j, (Hg G col j).edgeSet = ↑(G.edgeFinset.filter (fun e => col e ≠ j)) := by
    intro j; ext e
    induction e using Sym2.ind with
    | h a b => simp [Hg]
  have hcard : ∀ j, (Hg G col j).edgeSet.ncard = (G.edgeFinset.filter (fun e => col e ≠ j)).card := by
    intro j; rw [hEj, Set.ncard_coe_finset]
  have hsum : ∑ j : Fin 3, (G.edgeFinset.filter (fun e => col e ≠ j)).card
      = 2 * G.edgeFinset.card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    have : ∀ e, ∑ j : Fin 3, (if col e ≠ j then 1 else 0) = 2 := by
      intro e; generalize col e = x; revert x; decide
    rw [Finset.sum_congr rfl (fun e _ => this e)]
    simp [mul_comm]
  have hpair : ∃ j k : Fin 3, j ≠ k ∧
      3 * ((Hg G col j).edgeSet.ncard + (Hg G col k).edgeSet.ncard) ≤ 4 * G.edgeFinset.card := by
    rw [Fin.sum_univ_three] at hsum
    simp only [hcard]
    have : 3 * ((G.edgeFinset.filter (fun e => col e ≠ 0)).card +
          (G.edgeFinset.filter (fun e => col e ≠ 1)).card) ≤ 4 * G.edgeFinset.card ∨
        3 * ((G.edgeFinset.filter (fun e => col e ≠ 0)).card +
          (G.edgeFinset.filter (fun e => col e ≠ 2)).card) ≤ 4 * G.edgeFinset.card ∨
        3 * ((G.edgeFinset.filter (fun e => col e ≠ 1)).card +
          (G.edgeFinset.filter (fun e => col e ≠ 2)).card) ≤ 4 * G.edgeFinset.card := by omega
    rcases this with h | h | h
    · exact ⟨0, 1, by decide, h⟩
    · exact ⟨0, 2, by decide, h⟩
    · exact ⟨1, 2, by decide, h⟩
  obtain ⟨j, k, hjk, hle⟩ := hpair
  obtain ⟨Fj, hFj1, hFj2, hFj3⟩ := cover_of_isCycles G (Hg G col j) (Hg_le G col j)
    (Hg_isCycles G hcubic col hcolv j)
  obtain ⟨Fk, hFk1, hFk2, hFk3⟩ := cover_of_isCycles G (Hg G col k) (Hg_le G col k)
    (Hg_isCycles G hcubic col hcolv k)
  refine ⟨Fj ∪ Fk, ⟨?_, ?_⟩, ?_⟩
  · intro C hC
    rcases Finset.mem_union.1 hC with h | h
    · exact hFj1 C h
    · exact hFk1 C h
  · intro e he
    by_cases hj : col e = j
    · have hk : col e ≠ k := by rw [hj]; exact hjk
      have : e ∈ (Hg G col k).edgeSet := by
        rw [hEj]; simp [he, hk]
      obtain ⟨C, hC, heC⟩ := hFk2 e this
      exact ⟨C, Finset.mem_union_right _ hC, heC⟩
    · have : e ∈ (Hg G col j).edgeSet := by
        rw [hEj]; simp [he, hj]
      obtain ⟨C, hC, heC⟩ := hFj2 e this
      exact ⟨C, Finset.mem_union_left _ hC, heC⟩
  · have := Finset.sum_union_inter (s₁ := Fj) (s₂ := Fk) (f := fun C => C.card)
    unfold coverLength at *
    omega
