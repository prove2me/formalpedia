-- Prove2me | solution 1 for R03CubicMatchingIntervalIntegration.matching_interval_tile_has_complement_two_factor
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:54:36.405967+00:00
-- url     : https://prove2.me/submissions/8ca97cce-b507-4572-9278-d0e8a8d67190

import Mathlib
import Definitions.Def_cubic_p3_partition_models

/-!
Candidate-only formalization of the classical Petersen/Tutte matching bridge:
a finite cubic graph whose deletion of every set of at most two vertices is
connected has a perfect matching, and the complement of that matching is a
spanning 2-factor.  This file does not address divisibility of the factor
cycles and therefore does not close the frozen P3-factor problem.
-/

namespace R03PerfectMatchingCandidate

open CubicP3Partition
open SimpleGraph
open scoped BigOperators

universe u

variable {V : Type u} [Fintype V]

noncomputable def boundaryDarts (G : SimpleGraph V) (K U : Finset V) : Finset (V × V) := by
  classical
  exact (K ×ˢ U).filter (fun p => G.Adj p.1 p.2)

lemma boundary_darts_card_ge_three
    {G : SimpleGraph V}
    (hconn : ThreeVertexConnected G)
    {K U : Finset V}
    (hK : K.Nonempty)
    (hKU : Disjoint K U)
    (hclosed : ∀ x ∈ K, ∀ y ∉ (K : Set V), y ∉ (U : Set V) → ¬ G.Adj x y)
    (hout : ∃ y, y ∉ (K : Set V) ∧ y ∉ (U : Set V)) :
    3 ≤ (boundaryDarts G K U).card := by
  classical
  by_contra hsmall
  have hle : (boundaryDarts G K U).card ≤ 2 := by omega
  let S : Finset V := (boundaryDarts G K U).image Prod.snd
  have hScard : S.card ≤ 2 := by
    dsimp [S]
    exact (Finset.card_image_le).trans hle
  have hSsub : S ⊆ U := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨d, hd, rfl⟩
    simp only [boundaryDarts, Finset.mem_filter, Finset.mem_product] at hd
    exact hd.1.2
  obtain ⟨x, hxK⟩ := hK
  obtain ⟨y, hyK, hyU⟩ := hout
  have hxS : x ∉ (S : Set V) := by
    intro hx
    exact (Finset.disjoint_left.mp hKU) hxK (hSsub hx)
  have hyS : y ∉ (S : Set V) := by
    intro hy
    exact hyU (hSsub hy)
  let T : Set V := {v : V | v ∉ S}
  have hGconn : (G.induce T).Connected := by
    dsimp [T]
    exact hconn.2 S hScard
  let xi : {v : V // v ∈ T} := ⟨x, hxS⟩
  let yi : {v : V // v ∈ T} := ⟨y, hyS⟩
  obtain ⟨p⟩ := hGconn.preconnected xi yi
  let q : G.Walk x y := by
    simpa [xi, yi] using p.map (Embedding.induce T).toHom
  obtain ⟨d, hd, hdfstK, hdsndnotK⟩ :=
    q.exists_boundary_dart (K : Set V) hxK hyK
  have hdsndS : d.snd ∉ (S : Set V) := by
    have hsupp : d.snd ∈ q.support :=
      q.dart_snd_mem_support_of_mem_darts hd
    have hsupp' : d.snd ∈ (p.map (Embedding.induce T).toHom).support := by
      simpa [q] using hsupp
    rw [Walk.support_map] at hsupp'
    rcases List.mem_map.mp hsupp' with ⟨z, hz, hzval⟩
    rw [← hzval]
    exact z.property
  have hdsndU : d.snd ∈ U := by
    by_contra hnot
    exact hclosed d.fst hdfstK d.snd hdsndnotK hnot d.adj
  have hdD : d.toProd ∈ boundaryDarts G K U := by
    simp only [boundaryDarts, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hdfstK, hdsndU⟩, d.adj⟩
  have hdsndS' : d.snd ∈ S := by
    dsimp [S]
    exact Finset.mem_image.mpr ⟨d.toProd, hdD, rfl⟩
  exact hdsndS hdsndS'

lemma boundary_darts_sum_le_three_mul
    {G : SimpleGraph V} (hG : Cubic G)
    {ι : Type u} (I : Finset ι) (K : ι → Finset V) (U : Finset V)
    (hdisj : (I : Set ι).PairwiseDisjoint (fun i => (K i : Set V))) :
    (∑ i ∈ I, (boundaryDarts G (K i) U).card) ≤ 3 * U.card := by
  classical
  let B : Finset (Σ i : ι, V × V) := I.sigma (fun i => boundaryDarts G (K i) U)
  let T : Finset (Σ w : V, V) := U.sigma (fun w => G.neighborFinset w)
  let f : (Σ i : ι, V × V) → (Σ w : V, V) := fun z => ⟨z.2.2, z.2.1⟩
  have hfmem : ∀ z : (Σ i : ι, V × V), z ∈ B → f z ∈ T := by
    intro z hz
    have hz' := (Finset.mem_sigma.mp hz).2
    simp only [boundaryDarts, Finset.mem_filter, Finset.mem_product] at hz'
    apply Finset.mem_sigma.mpr
    refine ⟨hz'.1.2, ?_⟩
    exact (G.mem_neighborFinset _ _).2 hz'.2.symm
  let F : (↥B) → (↥T) := fun z => ⟨f z.1, hfmem z.1 z.2⟩
  have hFinj : Function.Injective F := by
    intro a b hab
    rcases a with ⟨⟨i, p⟩, ha⟩
    rcases b with ⟨⟨j, q⟩, hb⟩
    have hfpq : f ⟨i, p⟩ = f ⟨j, q⟩ := congrArg Subtype.val hab
    have hp2 : p.2 = q.2 := congrArg Sigma.fst hfpq
    have hp1 : p.1 = q.1 := congrArg Sigma.snd hfpq
    have hpi : p.1 ∈ K i := by
      have h := (Finset.mem_sigma.mp ha).2
      simp only [boundaryDarts, Finset.mem_filter, Finset.mem_product] at h
      exact h.1.1
    have hqj : q.1 ∈ K j := by
      have h := (Finset.mem_sigma.mp hb).2
      simp only [boundaryDarts, Finset.mem_filter, Finset.mem_product] at h
      exact h.1.1
    have hij : i = j := by
      by_contra hne
      have hiI : i ∈ I := (Finset.mem_sigma.mp ha).1
      have hjI : j ∈ I := (Finset.mem_sigma.mp hb).1
      have hd := hdisj (by simpa using hiI) (by simpa using hjI) hne
      have hnot : p.1 ∉ (K j : Set V) := Set.disjoint_left.mp hd hpi
      exact hnot (hp1 ▸ hqj)
    have hpq : p = q := Prod.ext hp1 hp2
    apply Subtype.ext
    cases hij
    exact congrArg (fun r => Sigma.mk i r) hpq
  have hcard := Fintype.card_le_of_injective F hFinj
  calc
    (∑ i ∈ I, (boundaryDarts G (K i) U).card) = B.card := by
      simp [B, Finset.card_sigma]
    _ = Fintype.card (↥B) := (Fintype.card_coe B).symm
    _ ≤ Fintype.card (↥T) := hcard
    _ = T.card := Fintype.card_coe T
    _ = (∑ w ∈ U, (G.neighborFinset w).card) := by
      simp [T, Finset.card_sigma]
    _ = ∑ w ∈ U, SimpleGraph.degree G w := by
      apply Finset.sum_congr rfl
      intro w hw
      exact G.card_neighborFinset_eq_degree w
    _ = 3 * U.card := by
      rw [show (∑ w ∈ U, SimpleGraph.degree G w) = ∑ _w ∈ U, 3 by
        apply Finset.sum_congr rfl
        intro w hw
        have hdeg : SimpleGraph.degree G w = 3 := by
          rw [SimpleGraph.degree, SimpleGraph.neighborFinset_def, Set.toFinset_card,
            ← Nat.card_eq_fintype_card]
          change Nat.card {z : V // G.Adj w z} = 3
          exact hG w
        exact hdeg]
      simp [Nat.mul_comm]


noncomputable def deletedGraph (G : SimpleGraph V) (U : Finset V) :
    SimpleGraph ↑((⊤ : G.Subgraph).deleteVerts (U : Set V)).verts :=
  ((⊤ : G.Subgraph).deleteVerts (U : Set V)).coe

noncomputable def componentFinset (G : SimpleGraph V) (U : Finset V)
    (c : (deletedGraph G U).ConnectedComponent) : Finset V := by
  classical
  exact c.supp.toFinset.image (fun x => x.1)

lemma componentFinset_nonempty (G : SimpleGraph V) (U : Finset V)
    (c : (deletedGraph G U).ConnectedComponent) :
    (componentFinset G U c).Nonempty := by
  classical
  rw [componentFinset]
  apply Finset.image_nonempty.mpr
  exact Set.toFinset_nonempty.mpr (ConnectedComponent.nonempty_supp c)

lemma componentFinset_disjoint (G : SimpleGraph V) (U : Finset V)
    (c : (deletedGraph G U).ConnectedComponent) :
    Disjoint (componentFinset G U c) U := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxK hxU
  rcases Finset.mem_image.mp hxK with ⟨z, hz, rfl⟩
  have hzU : z.1 ∉ (U : Set V) := by
    have hzvert := z.property
    change z.1 ∈ ((⊤ : G.Subgraph).deleteVerts (U : Set V)).verts at hzvert
    simpa [SimpleGraph.Subgraph.deleteVerts_verts] using hzvert
  exact hzU hxU

lemma componentFinset_pairwise_disjoint (G : SimpleGraph V) (U : Finset V)
    {ι : Type u} (I : Finset ι) (c : ι → (deletedGraph G U).ConnectedComponent)
    (hc : (I : Set ι).Pairwise (fun i j => c i ≠ c j)) :
    (I : Set ι).PairwiseDisjoint (fun i => (componentFinset G U (c i) : Set V)) := by
  classical
  intro i hi j hj hij
  change Disjoint (componentFinset G U (c i) : Set V) (componentFinset G U (c j) : Set V)
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases Finset.mem_image.mp hxi with ⟨z, hz, hzval⟩
  rcases Finset.mem_image.mp hxj with ⟨w, hw, hwval⟩
  have hzw : z = w := by
    apply Subtype.ext
    exact hzval.trans hwval.symm
  have hcommon : z ∈ (c i).supp ∧ z ∈ (c j).supp := by
    exact ⟨by simpa using hz, by simpa [hzw] using hw⟩
  exact (hc hi hj hij) (SimpleGraph.ConnectedComponent.eq_of_common_vertex hcommon.1 hcommon.2)

lemma componentFinset_closed (G : SimpleGraph V) (U : Finset V)
    (c : (deletedGraph G U).ConnectedComponent) :
    ∀ x ∈ componentFinset G U c, ∀ y ∉ (componentFinset G U c : Set V),
      y ∉ (U : Set V) → ¬ G.Adj x y := by
  classical
  intro x hx y hyK hyU hxy
  rcases Finset.mem_image.mp hx with ⟨z, hz, hzval⟩
  have hzsupp : z ∈ c.supp := by simpa using hz
  have hyvert : y ∈ ((⊤ : G.Subgraph).deleteVerts (U : Set V)).verts := by
    simp [SimpleGraph.Subgraph.deleteVerts_verts, hyU]
  let y' : ↑((⊤ : G.Subgraph).deleteVerts (U : Set V)).verts := ⟨y, hyvert⟩
  have hzU : z.1 ∉ (U : Set V) := by
    simpa [SimpleGraph.Subgraph.deleteVerts_verts] using z.property
  have hy'U : (y' : V) ∉ (U : Set V) := by
    simpa [SimpleGraph.Subgraph.deleteVerts_verts] using y'.property
  have hadjH : (deletedGraph G U).Adj z y' := by
    change ((⊤ : G.Subgraph).deleteVerts (U : Set V)).Adj z y'
    apply SimpleGraph.Subgraph.deleteVerts_adj.mpr
    refine ⟨by simp, hzU, by simp, hy'U, ?_⟩
    change G.Adj z.1 y'
    rw [hzval]
    exact hxy
  have hy'supp : y' ∈ c.supp := (c.mem_supp_congr_adj hadjH).mp hzsupp
  apply hyK
  refine Finset.mem_image.mpr ⟨y', ?_, rfl⟩
  simpa using hy'supp

noncomputable def oddComponentFinset {W : Type u} (H : SimpleGraph W) [Finite W] :
    Finset H.ConnectedComponent :=
  (Set.toFinite H.oddComponents).toFinset

lemma oddComponentFinset_card (G : SimpleGraph V) (U : Finset V) :
    let H := deletedGraph G U
    (oddComponentFinset H).card = H.oddComponents.ncard := by
  classical
  dsimp [oddComponentFinset]
  exact (Set.ncard_eq_toFinset_card _).symm

lemma componentFinset_outside_of_two (G : SimpleGraph V) (U : Finset V)
    {ι : Type u} (I : Finset ι) (c : ι → (deletedGraph G U).ConnectedComponent)
    (hc : (I : Set ι).Pairwise (fun i j => c i ≠ c j))
    (hcard : 2 ≤ I.card) (i : ι) (hi : i ∈ I) :
    ∃ y, y ∉ (componentFinset G U (c i) : Set V) ∧ y ∉ (U : Set V) := by
  classical
  have hex : ∃ j ∈ I, c j ≠ c i := by
    by_contra hn
    push_neg at hn
    have hsub : I ⊆ {i} := by
      intro j hj
      simp only [Finset.mem_singleton]
      by_contra hji
      exact (hc (by simpa using hj) (by simpa using hi) hji) (hn j hj)
    have hle : I.card ≤ ({i} : Finset ι).card := Finset.card_le_card hsub
    have hle' : I.card ≤ 1 := by simpa using hle
    omega
  obtain ⟨j, hj, hji⟩ := hex
  obtain ⟨z, hz⟩ := (c j).nonempty_supp
  have hzU : z.1 ∉ (U : Set V) := by
    have hzvert := z.property
    change z.1 ∈ ((⊤ : G.Subgraph).deleteVerts (U : Set V)).verts at hzvert
    simpa [SimpleGraph.Subgraph.deleteVerts_verts] using hzvert
  refine ⟨z.1, ?_, hzU⟩
  intro hzK
  rcases Finset.mem_image.mp hzK with ⟨w, hw, hwval⟩
  have hzw : z = w := by
    apply Subtype.ext
    exact hwval.symm
  have hcommon : z ∈ (c j).supp ∧ z ∈ (c i).supp := by
    exact ⟨hz, by simpa [hzw] using hw⟩
  exact hji (SimpleGraph.ConnectedComponent.eq_of_common_vertex hcommon.1 hcommon.2)


theorem no_finite_tutte_violator
    {G : SimpleGraph V} (hG : Cubic G) (hconn : ThreeVertexConnected G)
    (hEven : Even (Nat.card V)) :
    ∀ U : Finset V,
      ¬ U.card < (deletedGraph G U).oddComponents.ncard := by
  intro U hviol
  classical
  let H := deletedGraph G U
  let I : Finset H.ConnectedComponent := oddComponentFinset H
  have hIcard : I.card = H.oddComponents.ncard := by
    dsimp [I]
    exact (Set.ncard_eq_toFinset_card _).symm
  have hIgt : U.card < I.card := by
    rw [hIcard]
    exact hviol
  by_cases hI2 : 2 ≤ I.card
  · have hpair : (I : Set H.ConnectedComponent).Pairwise (fun c d => c ≠ d) := by
      intro c hc d hd hcd
      exact hcd
    have hdisj : (I : Set H.ConnectedComponent).PairwiseDisjoint
        (fun c => (componentFinset G U c : Set V)) := by
      exact componentFinset_pairwise_disjoint G U I (fun c => c) hpair
    have hlow : 3 * I.card ≤
        ∑ c ∈ I, (boundaryDarts G (componentFinset G U c) U).card := by
      calc
        3 * I.card = ∑ _c ∈ I, 3 := by simp [Nat.mul_comm]
        _ ≤ ∑ c ∈ I, (boundaryDarts G (componentFinset G U c) U).card := by
          apply Finset.sum_le_sum
          intro c hc
          exact boundary_darts_card_ge_three hconn
            (componentFinset_nonempty G U c)
            (componentFinset_disjoint G U c)
            (componentFinset_closed G U c)
            (componentFinset_outside_of_two G U I (fun c => c) hpair hI2 c hc)
    have hupp :
        (∑ c ∈ I, (boundaryDarts G (componentFinset G U c) U).card) ≤ 3 * U.card := by
      exact boundary_darts_sum_le_three_mul hG I (fun c => componentFinset G U c) U hdisj
    have : I.card ≤ U.card := by omega
    omega
  · have hIle : I.card ≤ 1 := by omega
    have hIeq : I.card = 1 := by omega
    have hUzero : U.card = 0 := by omega
    have hUempty : U = ∅ := Finset.card_eq_zero.mp hUzero
    subst U
    have hoddO : Odd H.oddComponents.ncard := by
      rw [← hIcard, hIeq]
      exact odd_one
    have hoddH : Odd
        (Nat.card (↥((⊤ : G.Subgraph).deleteVerts (∅ : Set V)).verts)) := by
      have hodd := (SimpleGraph.odd_ncard_oddComponents H).mp hoddO
      simpa [H, deletedGraph] using hodd
    have hEvenH : Even
        (Nat.card (↥((⊤ : G.Subgraph).deleteVerts (∅ : Set V)).verts)) := by
      let e : (↥((⊤ : G.Subgraph).deleteVerts (∅ : Set V)).verts) ≃ V := {
        toFun := fun v => v.1
        invFun := fun v => ⟨v, by simp⟩
        left_inv := by intro v; apply Subtype.ext; rfl
        right_inv := by intro v; rfl }
      rw [Nat.card_congr e]
      exact hEven
    exact (Nat.not_even_iff_odd.mpr hoddH) hEvenH

lemma oddComponents_ncard_eq_of_iso {W : Type u} {X : Type u}
    [Finite W] [Finite X] {H : SimpleGraph W} {K : SimpleGraph X}
    (e : H ≃g K) : H.oddComponents.ncard = K.oddComponents.ncard := by
  classical
  let eo : H.oddComponents ≃ K.oddComponents :=
    Equiv.subtypeEquiv e.connectedComponentEquiv (fun c => by
      change Odd c.supp.ncard ↔ Odd (e.connectedComponentEquiv c).supp.ncard
      have hs : c.supp.ncard = (e.connectedComponentEquiv c).supp.ncard := by
        change Nat.card c.supp = Nat.card (e.connectedComponentEquiv c).supp
        exact Nat.card_congr (c.isoEquivSupp e)
      rw [hs])
  exact Nat.card_congr eo

def deletedGraphIso {G : SimpleGraph V} {U : Finset V} {u : Set V}
    (h : (U : Set V) = u) :
    deletedGraph G U ≃g ((⊤ : G.Subgraph).deleteVerts u).coe := by
  classical
  let eV : (↥((⊤ : G.Subgraph).deleteVerts (U : Set V)).verts) ≃
      (↥((⊤ : G.Subgraph).deleteVerts u).verts) := {
    toFun := fun x => ⟨x.1, by simpa [SimpleGraph.Subgraph.deleteVerts_verts, h] using x.2⟩
    invFun := fun x => ⟨x.1, by simpa [SimpleGraph.Subgraph.deleteVerts_verts, h] using x.2⟩
    left_inv := by intro x; apply Subtype.ext; rfl
    right_inv := by intro x; apply Subtype.ext; rfl }
  exact {
    toFun := eV
    invFun := eV.symm
    left_inv := eV.left_inv
    right_inv := eV.right_inv
    map_rel_iff' := by
      intro x y
      change ((⊤ : G.Subgraph).deleteVerts u).Adj (eV x) (eV y) ↔
        ((⊤ : G.Subgraph).deleteVerts (U : Set V)).Adj x y
      simp only [SimpleGraph.Subgraph.deleteVerts_adj]
      simp [eV, h] }

theorem cubic_three_connected_has_perfect_matching
    {G : SimpleGraph V} (hG : Cubic G) (hconn : ThreeVertexConnected G)
    (hEven : Even (Nat.card V)) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  apply (SimpleGraph.tutte).2
  intro u huv
  let huFinite : u.Finite := Set.toFinite u
  let U : Finset V := huFinite.toFinset
  have hUset : (U : Set V) = u := huFinite.coe_toFinset
  have hUcard : U.card = u.ncard := (Set.ncard_eq_toFinset_card u huFinite).symm
  have hiso := deletedGraphIso (G := G) hUset
  have hoddcard : (deletedGraph G U).oddComponents.ncard =
      ((⊤ : G.Subgraph).deleteVerts u).coe.oddComponents.ncard :=
    oddComponents_ncard_eq_of_iso hiso
  have hviol : U.card < (deletedGraph G U).oddComponents.ncard := by
    rw [hUcard, hoddcard]
    exact huv
  exact (no_finite_tutte_violator hG hconn hEven U) hviol

theorem cubic_three_connected_has_project_perfect_matching_of_even
    {G : SimpleGraph V} (hG : Cubic G) (hconn : ThreeVertexConnected G)
    (hEven : Even (Nat.card V)) :
    ∃ M : SimpleGraph V, PerfectMatching G M := by
  obtain ⟨Msub, hMsub⟩ := cubic_three_connected_has_perfect_matching hG hconn hEven
  let M : SimpleGraph V := Msub.spanningCoe
  refine ⟨M, Msub.spanningCoe_le, ?_⟩
  intro v
  letI : Fintype {w : V // M.Adj v w} := Fintype.ofFinite _
  rw [CubicP3Partition.degree, Nat.card_eq_fintype_card]
  apply Fintype.card_eq_one_iff.mpr
  obtain ⟨w, hw, hwu⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hMsub) v
  refine ⟨⟨w, ?_⟩, ?_⟩
  · change Msub.spanningCoe.Adj v w
    rw [SimpleGraph.Subgraph.spanningCoe_adj]
    exact hw
  · intro z
    apply Subtype.ext
    apply hwu
    change Msub.Adj v z.1
    exact z.2

lemma cubic_card_even (G : SimpleGraph V) (hG : Cubic G) :
    Even (Nat.card V) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  have hsum : ∑ v, SimpleGraph.degree G v = 3 * Fintype.card V := by
    calc
      ∑ v, SimpleGraph.degree G v = ∑ v, 3 := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [SimpleGraph.degree, SimpleGraph.neighborFinset_def, Set.toFinset_card]
        rw [← Nat.card_eq_fintype_card]
        change Nat.card {z : V // G.Adj v z} = 3
        exact hG v
      _ = 3 * Fintype.card V := by simp [Nat.mul_comm]
  have hhand : ∑ v, SimpleGraph.degree G v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  have hmul : 3 * Fintype.card V = 2 * G.edgeFinset.card := hsum.symm.trans hhand
  have hevenCard : Even (Fintype.card V) := by
    apply Nat.even_iff.mpr
    omega
  simpa only [Nat.card_eq_fintype_card] using hevenCard

 theorem cubic_three_connected_has_project_perfect_matching
    {G : SimpleGraph V} (hG : Cubic G) (hconn : ThreeVertexConnected G) :
    ∃ M : SimpleGraph V, PerfectMatching G M := by
  exact cubic_three_connected_has_project_perfect_matching_of_even hG hconn
    (cubic_card_even G hG)

def complementFNeighbors (G M : SimpleGraph V) (v : V) :=
  {w : V // G.Adj v w ∧ ¬ M.Adj v w}

noncomputable def complementNeighborEquiv
    (G M : SimpleGraph V) (v : V) (hMsub : M ≤ G) :
    ({w : V // M.Adj v w} ⊕ complementFNeighbors G M v) ≃
      {w : V // G.Adj v w} := by
  classical
  let toFun : ({w : V // M.Adj v w} ⊕ complementFNeighbors G M v) →
      {w : V // G.Adj v w} := fun x =>
    match x with
    | Sum.inl w => ⟨w.1, hMsub w.2⟩
    | Sum.inr w => ⟨w.1, w.2.1⟩
  let invFun : {w : V // G.Adj v w} →
      ({w : V // M.Adj v w} ⊕ complementFNeighbors G M v) := fun w =>
    if h : M.Adj v w.1 then
      Sum.inl ⟨w.1, h⟩
    else
      Sum.inr ⟨w.1, w.2, h⟩
  refine {
    toFun := toFun
    invFun := invFun
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    rcases x with w | w
    · simp [toFun, invFun, w.property]
    · have hn : ¬ M.Adj v w.1 := w.2.2
      simp only [invFun, dif_neg hn, toFun]
      apply congrArg Sum.inr
      exact Subtype.ext (by rfl)
  · intro w
    by_cases h : M.Adj v w.1
    · simp [toFun, invFun, h]
    · simp [toFun, invFun, h]

lemma complementFNeighbors_card
    {G M : SimpleGraph V} {v : V}
    (hMsub : M ≤ G)
    (hGdeg : CubicP3Partition.degree G v = 3)
    (hMdeg : CubicP3Partition.degree M v = 1) :
    Nat.card (complementFNeighbors G M v) = 2 := by
  classical
  letI : Fintype {w : V // G.Adj v w} := Fintype.ofFinite _
  letI : Fintype {w : V // M.Adj v w} := Fintype.ofFinite _
  let s : Finset V := (G.neighborFinset v).filter (fun w => ¬ M.Adj v w)
  letI : Fintype (complementFNeighbors G M v) :=
    Fintype.subtype s (by
      intro w
      simp [s, complementFNeighbors])
  let e := complementNeighborEquiv G M v hMsub
  have hcard := Fintype.card_congr e
  have hGcard : Fintype.card {w : V // G.Adj v w} = 3 := by
    rw [← Nat.card_eq_fintype_card]
    change CubicP3Partition.degree G v = 3
    exact hGdeg
  have hMcard : Fintype.card {w : V // M.Adj v w} = 1 := by
    rw [← Nat.card_eq_fintype_card]
    change CubicP3Partition.degree M v = 1
    exact hMdeg
  rw [Fintype.card_sum] at hcard
  have hFcard : Fintype.card (complementFNeighbors G M v) = 2 := by
    omega
  simpa [Nat.card_eq_fintype_card] using hFcard

lemma matchingComplement_adj_iff_local
    (G M : SimpleGraph V) (v w : V) :
    (matchingComplement G M).Adj v w ↔ G.Adj v w ∧ ¬ M.Adj v w := by
  rw [matchingComplement, SimpleGraph.inf_adj, SimpleGraph.compl_adj]
  constructor
  · rintro ⟨hG, _hne, hM⟩
    exact ⟨hG, hM⟩
  · rintro ⟨hG, hM⟩
    refine ⟨hG, ?_, hM⟩
    intro hvw
    subst w
    exact G.loopless.irrefl v hG

lemma matchingComplement_degree_two_local
    {G M : SimpleGraph V}
    (hG : Cubic G)
    (hM : PerfectMatching G M) (v : V) :
    CubicP3Partition.degree (matchingComplement G M) v = 2 := by
  classical
  let e : {w : V // (matchingComplement G M).Adj v w} ≃
      complementFNeighbors G M v :=
    { toFun := fun w => ⟨w.1, (matchingComplement_adj_iff_local G M v w.1).mp w.2⟩
      invFun := fun w => ⟨w.1, (matchingComplement_adj_iff_local G M v w.1).mpr w.2⟩
      left_inv := by intro w; rfl
      right_inv := by intro w; rfl }
  calc
    CubicP3Partition.degree (matchingComplement G M) v =
        Nat.card {w : V // (matchingComplement G M).Adj v w} := rfl
    _ = Nat.card (complementFNeighbors G M v) := Nat.card_congr e
    _ = 2 := complementFNeighbors_card hM.1 (hG v) (hM.2 v)

theorem matchingComplement_twoFactor_of_cubic_perfectMatching_local
    {G M : SimpleGraph V}
    (hG : Cubic G) (hM : PerfectMatching G M) :
    TwoFactor G (matchingComplement G M) := by
  refine ⟨?_, ?_⟩
  · exact inf_le_left
  · intro v
    exact matchingComplement_degree_two_local hG hM v

theorem cubic_three_connected_has_complement_two_factor
    {G : SimpleGraph V} (hG : Cubic G) (hconn : ThreeVertexConnected G) :
    ∃ M : SimpleGraph V,
      PerfectMatching G M ∧ TwoFactor G (matchingComplement G M) := by
  obtain ⟨M, hM⟩ := cubic_three_connected_has_project_perfect_matching hG hconn
  exact ⟨M, hM, matchingComplement_twoFactor_of_cubic_perfectMatching_local hG hM⟩

#print axioms boundary_darts_card_ge_three
#print axioms boundary_darts_sum_le_three_mul
#print axioms no_finite_tutte_violator
#print axioms cubic_three_connected_has_perfect_matching
#print axioms cubic_three_connected_has_project_perfect_matching
#print axioms cubic_three_connected_has_complement_two_factor

end R03PerfectMatchingCandidate

namespace R03FixedPerfectMatchingBridge

open CubicP3Partition

universe u

variable {V : Type u} [Fintype V]

def FAdj (G M : SimpleGraph V) (a b : V) : Prop :=
  G.Adj a b ∧ ¬ M.Adj a b

def IsMatchingRelation (M : SimpleGraph V) : Prop :=
  ∀ ⦃v a b : V⦄, M.Adj v a → M.Adj v b → a = b

def P3PathProp (G : SimpleGraph V) (a b c : V) : Prop :=
  a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ G.Adj a b ∧ G.Adj b c

def IntervalTile (G M : SimpleGraph V) (a b c : V) : Prop :=
  a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    ((FAdj G M a b ∧ FAdj G M b c) ∨
      (M.Adj a b ∧ FAdj G M b c) ∨
      (FAdj G M a b ∧ M.Adj b c))

structure IntervalTileFactor (G M : SimpleGraph V) where
  blockCount : Nat
  place : (Fin blockCount × Fin 3) ≃ V
  tile : ∀ i : Fin blockCount,
    IntervalTile G M (place (i, 0)) (place (i, 1)) (place (i, 2))

lemma perfectMatching_isMatchingRelation
    {G M : SimpleGraph V} (hM : PerfectMatching G M) :
    IsMatchingRelation M := by
  classical
  intro v a b hav hbv
  have hcard : Fintype.card {w : V // M.Adj v w} = 1 := by
    simpa [CubicP3Partition.degree, Nat.card_eq_fintype_card] using hM.2 v
  obtain ⟨w, hw⟩ := (Fintype.card_eq_one_iff.mp hcard)
  have ha : (⟨a, hav⟩ : {w : V // M.Adj v w}) = w := hw _
  have hb : (⟨b, hbv⟩ : {w : V // M.Adj v w}) = w := hw _
  exact congrArg Subtype.val (ha.trans hb.symm)

lemma p3Path_iff_intervalTile
    (G M : SimpleGraph V)
    (hMsub : M ≤ G)
    (hMmatch : IsMatchingRelation M)
    {a b c : V} :
    P3PathProp G a b c ↔ IntervalTile G M a b c := by
  constructor
  · rintro ⟨hab_ne, hbc_ne, hac_ne, hab, hbc⟩
    refine ⟨hab_ne, hbc_ne, hac_ne, ?_⟩
    by_cases hmab : M.Adj a b
    · right
      left
      refine ⟨hmab, ?_⟩
      by_cases hmbc : M.Adj b c
      · exact False.elim (hac_ne (hMmatch ((M.adj_comm a b).mp hmab) hmbc))
      · exact ⟨hbc, hmbc⟩
    · by_cases hmbc : M.Adj b c
      · right
        exact Or.inr ⟨⟨hab, hmab⟩, hmbc⟩
      · left
        exact ⟨⟨hab, hmab⟩, ⟨hbc, hmbc⟩⟩
  · rintro ⟨hab_ne, hbc_ne, hac_ne, htiles⟩
    refine ⟨hab_ne, hbc_ne, hac_ne, ?_⟩
    rcases htiles with hff | hmf | hfm
    · exact ⟨hff.1.1, hff.2.1⟩
    · exact ⟨hMsub hmf.1, hmf.2.1⟩
    · exact ⟨hfm.1.1, hMsub hfm.2⟩

lemma fin3_pairwise_distinct {α : Type u} (i : α) :
    (i, (0 : Fin 3)) ≠ (i, (1 : Fin 3)) ∧
    (i, (1 : Fin 3)) ≠ (i, (2 : Fin 3)) ∧
    (i, (0 : Fin 3)) ≠ (i, (2 : Fin 3)) := by
  simp

lemma nonempty_p3Factor_iff_nonempty_intervalTileFactor
    (G M : SimpleGraph V)
    (hMsub : M ≤ G)
    (hMmatch : IsMatchingRelation M) :
    Nonempty (CubicP3Partition.P3Factor G) ↔
      Nonempty (IntervalTileFactor G M) := by
  constructor
  · rintro ⟨p⟩
    refine ⟨{
      blockCount := p.blockCount
      place := p.place
      tile := ?_ }⟩
    intro i
    apply (p3Path_iff_intervalTile G M hMsub hMmatch).mp
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      have : (i, (0 : Fin 3)) = (i, (1 : Fin 3)) := p.place.injective h
      exact (fin3_pairwise_distinct i).1 this
    · intro h
      have : (i, (1 : Fin 3)) = (i, (2 : Fin 3)) := p.place.injective h
      exact (fin3_pairwise_distinct i).2.1 this
    · intro h
      have : (i, (0 : Fin 3)) = (i, (2 : Fin 3)) := p.place.injective h
      exact (fin3_pairwise_distinct i).2.2 this
    · exact ⟨p.edge01 i, p.edge12 i⟩
  · rintro ⟨t⟩
    refine ⟨{
      blockCount := t.blockCount
      place := t.place
      edge01 := ?_
      edge12 := ?_ }⟩
    · intro i
      have hp := (p3Path_iff_intervalTile G M hMsub hMmatch).mpr (t.tile i)
      exact hp.2.2.2.1
    · intro i
      have hp := (p3Path_iff_intervalTile G M hMsub hMmatch).mpr (t.tile i)
      exact hp.2.2.2.2

/-- Once a perfect matching is supplied, existence of a tile factor is an
exact reformulation of existence of the frozen P3Factor witness. -/
theorem nonempty_p3Factor_iff_exists_perfectMatching_tileFactor
    (G : SimpleGraph V)
    (hExists : ∃ M : SimpleGraph V, PerfectMatching G M) :
    Nonempty (CubicP3Partition.P3Factor G) ↔
      ∃ M : SimpleGraph V,
        PerfectMatching G M ∧ Nonempty (IntervalTileFactor G M) := by
  constructor
  · intro hp
    obtain ⟨M, hM⟩ := hExists
    refine ⟨M, hM, ?_⟩
    exact (nonempty_p3Factor_iff_nonempty_intervalTileFactor G M hM.1
      (perfectMatching_isMatchingRelation hM)).mp hp
  · rintro ⟨M, hM, ht⟩
    exact (nonempty_p3Factor_iff_nonempty_intervalTileFactor G M hM.1
      (perfectMatching_isMatchingRelation hM)).mpr ht

#print axioms perfectMatching_isMatchingRelation
#print axioms nonempty_p3Factor_iff_exists_perfectMatching_tileFactor

end R03FixedPerfectMatchingBridge

namespace R03CubicMatchingIntervalIntegration

open CubicP3Partition
open SimpleGraph

universe u

variable {V : Type u} [Fintype V]

/-- Candidate composition of the cubic Tutte/Petersen bridge with the exact
fixed-perfect-matching interval-tile reformulation.  The remaining tile-factor
existence is deliberately left as the right-hand obligation. -/
theorem cubic_three_connected_p3_factor_iff_matching_interval_tile
    (G : SimpleGraph V)
    (hG : Cubic G) (hconn : ThreeVertexConnected G) :
    Nonempty (P3Factor G) ↔
      ∃ M : SimpleGraph V,
        PerfectMatching G M ∧
        Nonempty (R03FixedPerfectMatchingBridge.IntervalTileFactor G M) := by
  apply R03FixedPerfectMatchingBridge.nonempty_p3Factor_iff_exists_perfectMatching_tileFactor
  exact R03PerfectMatchingCandidate.cubic_three_connected_has_project_perfect_matching
    hG hconn


end R03CubicMatchingIntervalIntegration

open R03CubicMatchingIntervalIntegration
open CubicP3Partition
open SimpleGraph
open scoped BigOperators
universe u
variable {V : Type u} [Fintype V]
theorem solution
    (G : SimpleGraph V)
    (hG : Cubic G)
    {M : SimpleGraph V} (hM : PerfectMatching G M) :
    TwoFactor G (matchingComplement G M) := by
  exact R03PerfectMatchingCandidate.matchingComplement_twoFactor_of_cubic_perfectMatching_local
    hG hM

