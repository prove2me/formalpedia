-- Prove2me | solution 1 for R03CubicMatchingTwoCycleIntegration.cubic_three_connected_two_cycle_profile_p3_factor
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:54:46.290971+00:00
-- url     : https://prove2.me/submissions/9691f201-5109-4f09-917e-36d79ef044e2

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

namespace CubicP3Partition
open SimpleGraph
universe u
set_option maxHeartbeats 1000000

/-- Candidate assembly lemma: three local ordered paths in each residual block,
    plus a two-edge exceptional block, give a canonical P3 factor. -/
theorem R03SP01ThreePieceCrossAssembly
    {A B : Type u} [Fintype A] [Fintype B]
    (G : SimpleGraph (A ⊕ B))
    (kA kB : Nat)
    (eA : (Fin (kA * 3) ⊕ Fin 1) ≃ A)
    (eB : (Fin (kB * 3) ⊕ Fin 2) ≃ B)
    (edgeA : ∀ b : Fin kA,
      G.Adj (Sum.inl (eA (Sum.inl (finProdFinEquiv (b, 0)))))
        (Sum.inl (eA (Sum.inl (finProdFinEquiv (b, 1))))) ∧
      G.Adj (Sum.inl (eA (Sum.inl (finProdFinEquiv (b, 1)))))
        (Sum.inl (eA (Sum.inl (finProdFinEquiv (b, 2))))))
    (edgeB : ∀ b : Fin kB,
      G.Adj (Sum.inr (eB (Sum.inl (finProdFinEquiv (b, 0)))))
        (Sum.inr (eB (Sum.inl (finProdFinEquiv (b, 1))))) ∧
      G.Adj (Sum.inr (eB (Sum.inl (finProdFinEquiv (b, 1)))))
        (Sum.inr (eB (Sum.inl (finProdFinEquiv (b, 2))))))
    (cross01 : G.Adj (Sum.inl (eA (Sum.inr 0)))
      (Sum.inr (eB (Sum.inr 0))))
    (cross12 : G.Adj (Sum.inr (eB (Sum.inr 0)))
      (Sum.inr (eB (Sum.inr 1)))) :
    Nonempty (P3Factor G) := by
  let crossPlace : Fin 3 → A ⊕ B := fun j =>
    if j = 0 then Sum.inl (eA (Sum.inr 0))
    else if j = 1 then Sum.inr (eB (Sum.inr 0))
    else Sum.inr (eB (Sum.inr 1))
  let targetFun : ((Fin 3 ⊕ Fin (kA * 3)) ⊕ Fin (kB * 3)) → A ⊕ B := fun x =>
    match x with
    | Sum.inl (Sum.inl j) => crossPlace j
    | Sum.inl (Sum.inr a) => Sum.inl (eA (Sum.inl a))
    | Sum.inr b => Sum.inr (eB (Sum.inl b))
  let targetInv : (A ⊕ B) → ((Fin 3 ⊕ Fin (kA * 3)) ⊕ Fin (kB * 3)) := fun z =>
    match z with
    | Sum.inl a =>
      match eA.symm a with
      | Sum.inl r => Sum.inl (Sum.inr r)
      | Sum.inr _ => Sum.inl (Sum.inl 0)
    | Sum.inr b =>
      match eB.symm b with
      | Sum.inl r => Sum.inr r
      | Sum.inr r => if r = 0 then Sum.inl (Sum.inl 1) else Sum.inl (Sum.inl 2)
  let targetEquiv : ((Fin 3 ⊕ Fin (kA * 3)) ⊕ Fin (kB * 3)) ≃ (A ⊕ B) := {
    toFun := targetFun
    invFun := targetInv
    left_inv := by
      intro x
      rcases x with x | x
      · rcases x with x | x
        · fin_cases x <;> simp [targetInv, targetFun, crossPlace]
        · simp [targetInv, targetFun, crossPlace]
      · simp [targetInv, targetFun, crossPlace]
    right_inv := by
      intro z
      rcases z with z | z
      · generalize hr : eA.symm z = r
        rcases r with r | r
        · have hz : z = eA (Sum.inl r) := by
            rw [← eA.apply_symm_apply z, hr]
          simp [targetInv, targetFun, crossPlace, hz]
        · have hz : z = eA (Sum.inr r) := by
            rw [← eA.apply_symm_apply z, hr]
          simpa [targetInv, targetFun, crossPlace, hz] using
            (Subsingleton.elim (0 : Fin 1) r)
      · generalize hr : eB.symm z = r
        rcases r with r | r
        · have hz : z = eB (Sum.inl r) := by
            rw [← eB.apply_symm_apply z, hr]
          simp [targetInv, targetFun, crossPlace, hz]
        · have hz : z = eB (Sum.inr r) := by
            rw [← eB.apply_symm_apply z, hr]
          fin_cases r <;> simp [targetInv, targetFun, crossPlace, hz]
  }
  let indexFun : (Fin (1 + kA + kB) × Fin 3) →
      ((Fin 3 ⊕ Fin (kA * 3)) ⊕ Fin (kB * 3)) := fun q =>
    Fin.addCases
      (fun b => Fin.addCases
        (fun _ => Sum.inl (Sum.inl q.2))
        (fun a => Sum.inl (Sum.inr (finProdFinEquiv (a, q.2)))) b)
      (fun b => Sum.inr (finProdFinEquiv (b, q.2))) q.1
  let indexInv : (((Fin 3 ⊕ Fin (kA * 3)) ⊕ Fin (kB * 3))) →
      (Fin (1 + kA + kB) × Fin 3) := fun x =>
    match x with
    | Sum.inl (Sum.inl j) => (Fin.castAdd kB (Fin.castAdd kA 0), j)
    | Sum.inl (Sum.inr r) =>
      let p := finProdFinEquiv.symm r
      (Fin.castAdd kB (Fin.natAdd 1 p.1), p.2)
    | Sum.inr r =>
      let p := finProdFinEquiv.symm r
      (Fin.natAdd (1 + kA) p.1, p.2)
  let indexEquiv : (Fin (1 + kA + kB) × Fin 3) ≃
      ((Fin 3 ⊕ Fin (kA * 3)) ⊕ Fin (kB * 3)) := {
    toFun := indexFun
    invFun := indexInv
    left_inv := by
      intro q
      rcases q with ⟨b,j⟩
      refine Fin.addCases (fun b => ?_) (fun b => ?_) b
      · refine Fin.addCases (fun b => ?_) (fun b => ?_) b
        · fin_cases b
          simp [indexInv, indexFun]
        · have hprod := finProdFinEquiv.left_inv (b, j)
          have hprod' : (finProdFinEquiv (b, j)).divNat = b ∧
              (finProdFinEquiv (b, j)).modNat = j :=
            ⟨congrArg Prod.fst hprod, congrArg Prod.snd hprod⟩
          simp [indexInv, indexFun, Fin.addCases_left, Fin.addCases_right, hprod']
      · have hprod := finProdFinEquiv.left_inv (b, j)
        have hprod' : (finProdFinEquiv (b, j)).divNat = b ∧
            (finProdFinEquiv (b, j)).modNat = j :=
          ⟨congrArg Prod.fst hprod, congrArg Prod.snd hprod⟩
        simp [indexInv, indexFun, Fin.addCases_right, hprod']
    right_inv := by
      intro x
      rcases x with x | x
      · rcases x with x | x
        · simp [indexInv, indexFun]
        · simpa [indexInv, indexFun, Fin.addCases_left, Fin.addCases_right] using
            (finProdFinEquiv.right_inv x)
      · simpa [indexInv, indexFun, Fin.addCases_left, Fin.addCases_right] using
          (finProdFinEquiv.right_inv x)
  }
  let place : (Fin (1 + kA + kB) × Fin 3) ≃ (A ⊕ B) :=
    indexEquiv.trans targetEquiv
  refine ⟨{
    blockCount := 1 + kA + kB
    place := place
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro b
    refine Fin.addCases (fun b => ?_) (fun b => ?_) b
    · refine Fin.addCases (fun b => ?_) (fun b => ?_) b
      · fin_cases b
        simpa [place, indexEquiv, indexFun, targetEquiv, targetFun, crossPlace,
          Fin.addCases_left, Fin.addCases_right] using cross01
      · have h := (edgeA b).1
        simpa [place, indexEquiv, indexFun, targetEquiv, targetFun, crossPlace,
          finProdFinEquiv, Fin.addCases_left, Fin.addCases_right] using h
    · have h := (edgeB b).1
      simpa [place, indexEquiv, indexFun, targetEquiv, targetFun, crossPlace,
        finProdFinEquiv, Fin.addCases_left, Fin.addCases_right] using h
  · intro b
    refine Fin.addCases (fun b => ?_) (fun b => ?_) b
    · refine Fin.addCases (fun b => ?_) (fun b => ?_) b
      · fin_cases b
        simpa [place, indexEquiv, indexFun, targetEquiv, targetFun, crossPlace,
          Fin.addCases_left, Fin.addCases_right] using cross12
      · have h := (edgeA b).2
        simpa [place, indexEquiv, indexFun, targetEquiv, targetFun, crossPlace,
          finProdFinEquiv, Fin.addCases_left, Fin.addCases_right] using h
    · have h := (edgeB b).2
      simpa [place, indexEquiv, indexFun, targetEquiv, targetFun, crossPlace,
        finProdFinEquiv, Fin.addCases_left, Fin.addCases_right] using h

#print axioms R03SP01ThreePieceCrossAssembly

/-- Candidate two-cycle residue construction.  A cycle of order 1 modulo 3
    and a cycle of order 2 modulo 3 are cut at a cross edge and tiled by the
    preceding assembly lemma. -/
theorem R03SP01TwoCycleResidueAssembly
    {A B : Type u} [Fintype A] [Fintype B]
    (G : SimpleGraph (A ⊕ B))
    (kA kB : Nat)
    (eA : Fin (1 + kA * 3) ≃ A)
    (eB : Fin (2 + kB * 3) ≃ B)
    (cycleA : ∀ i : Fin (kA * 3 - 1),
      G.Adj (Sum.inl (eA ⟨1 + i.val, by omega⟩))
        (Sum.inl (eA ⟨1 + (i.val + 1), by omega⟩)))
    (cycleB : ∀ i : Fin (kB * 3 - 1),
      G.Adj (Sum.inr (eB ⟨2 + i.val, by omega⟩))
        (Sum.inr (eB ⟨2 + (i.val + 1), by omega⟩)))
    (cross01 : G.Adj (Sum.inl (eA 0)) (Sum.inr (eB 0)))
    (cross12 : G.Adj (Sum.inr (eB 0)) (Sum.inr (eB 1))) :
    Nonempty (P3Factor G) := by
  let shiftA : (Fin (kA * 3) ⊕ Fin 1) ≃ Fin (1 + kA * 3) :=
    finSumFinEquiv.trans (finAddFlip (m := kA * 3) (n := 1))
  let shiftB : (Fin (kB * 3) ⊕ Fin 2) ≃ Fin (2 + kB * 3) :=
    finSumFinEquiv.trans (finAddFlip (m := kB * 3) (n := 2))
  let blockA : (Fin (kA * 3) ⊕ Fin 1) ≃ A := shiftA.trans eA
  let blockB : (Fin (kB * 3) ⊕ Fin 2) ≃ B := shiftB.trans eB
  have hshiftA_left (r : Fin (kA * 3)) :
      shiftA (Sum.inl r) = Fin.natAdd 1 r := by
    simp [shiftA, finSumFinEquiv, finAddFlip]
  have hshiftA_right (r : Fin 1) :
      shiftA (Sum.inr r) = Fin.castAdd (kA * 3) r := by
    simp [shiftA, finSumFinEquiv, finAddFlip]
  have hshiftB_left (r : Fin (kB * 3)) :
      shiftB (Sum.inl r) = Fin.natAdd 2 r := by
    simp [shiftB, finSumFinEquiv, finAddFlip]
  have hshiftB_right (r : Fin 2) :
      shiftB (Sum.inr r) = Fin.castAdd (kB * 3) r := by
    simp [shiftB, finSumFinEquiv, finAddFlip]
  have hblockA (b : Fin kA) (j : Fin 3) :
      blockA (Sum.inl (finProdFinEquiv (b, j))) =
        eA (Fin.natAdd 1 (finProdFinEquiv (b, j))) := by
    simp only [blockA, Equiv.trans_apply]
    rw [hshiftA_left]
  have hblockB (b : Fin kB) (j : Fin 3) :
      blockB (Sum.inl (finProdFinEquiv (b, j))) =
        eB (Fin.natAdd 2 (finProdFinEquiv (b, j))) := by
    simp only [blockB, Equiv.trans_apply]
    rw [hshiftB_left]
  have hblockA0 : blockA (Sum.inr (0 : Fin 1)) = eA 0 := by
    simp only [blockA, Equiv.trans_apply]
    rw [hshiftA_right]
    rfl
  have hblockB0 : blockB (Sum.inr (0 : Fin 2)) = eB 0 := by
    simp only [blockB, Equiv.trans_apply]
    rw [hshiftB_right]
    rfl
  have hblockB1 : blockB (Sum.inr (1 : Fin 2)) = eB 1 := by
    simp only [blockB, Equiv.trans_apply]
    rw [hshiftB_right]
    apply congrArg eB
    apply Fin.ext
    norm_num [Nat.mod_eq_of_lt (by omega : 1 < 2 + kB * 3)]
  have hA : ∀ b : Fin kA,
      G.Adj (Sum.inl (blockA (Sum.inl (finProdFinEquiv (b, (0 : Fin 3))))))
        (Sum.inl (blockA (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))))) ∧
      G.Adj (Sum.inl (blockA (Sum.inl (finProdFinEquiv (b, (1 : Fin 3))))))
        (Sum.inl (blockA (Sum.inl (finProdFinEquiv (b, (2 : Fin 3)))))) := by
    intro b
    have hb := b.is_lt
    constructor
    · have hi : (finProdFinEquiv (b, (0 : Fin 3))).val + 1 < kA * 3 := by
        simp [finProdFinEquiv]
        omega
      have h := cycleA ⟨(finProdFinEquiv (b, (0 : Fin 3))).val, by omega⟩
      have h0 : blockA (Sum.inl (finProdFinEquiv (b, (0 : Fin 3)))) =
          eA ⟨1 + (finProdFinEquiv (b, (0 : Fin 3))).val, by omega⟩ := by
        rw [hblockA]
        apply congrArg eA
        apply Fin.ext
        rfl
      have h1 : blockA (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))) =
          eA ⟨1 + ((finProdFinEquiv (b, (0 : Fin 3))).val + 1), by omega⟩ := by
        rw [hblockA]
        apply congrArg eA
        apply Fin.ext
        simp [finProdFinEquiv]
        omega
      rw [h0, h1]
      exact h
    · have hi : (finProdFinEquiv (b, (1 : Fin 3))).val + 1 < kA * 3 := by
        simp [finProdFinEquiv]
        omega
      have h := cycleA ⟨(finProdFinEquiv (b, (1 : Fin 3))).val, by omega⟩
      have h1 : blockA (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))) =
          eA ⟨1 + (finProdFinEquiv (b, (1 : Fin 3))).val, by omega⟩ := by
        rw [hblockA]
        apply congrArg eA
        apply Fin.ext
        rfl
      have h2 : blockA (Sum.inl (finProdFinEquiv (b, (2 : Fin 3)))) =
          eA ⟨1 + ((finProdFinEquiv (b, (1 : Fin 3))).val + 1), by omega⟩ := by
        rw [hblockA]
        apply congrArg eA
        apply Fin.ext
        simp [finProdFinEquiv]
        omega
      rw [h1, h2]
      exact h
  have hB : ∀ b : Fin kB,
      G.Adj (Sum.inr (blockB (Sum.inl (finProdFinEquiv (b, (0 : Fin 3))))))
        (Sum.inr (blockB (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))))) ∧
      G.Adj (Sum.inr (blockB (Sum.inl (finProdFinEquiv (b, (1 : Fin 3))))))
        (Sum.inr (blockB (Sum.inl (finProdFinEquiv (b, (2 : Fin 3)))))) := by
    intro b
    have hb := b.is_lt
    constructor
    · have hi : (finProdFinEquiv (b, (0 : Fin 3))).val + 1 < kB * 3 := by
        simp [finProdFinEquiv]
        omega
      have h := cycleB ⟨(finProdFinEquiv (b, (0 : Fin 3))).val, by omega⟩
      have h0 : blockB (Sum.inl (finProdFinEquiv (b, (0 : Fin 3)))) =
          eB ⟨2 + (finProdFinEquiv (b, (0 : Fin 3))).val, by omega⟩ := by
        rw [hblockB]
        apply congrArg eB
        apply Fin.ext
        rfl
      have h1 : blockB (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))) =
          eB ⟨2 + ((finProdFinEquiv (b, (0 : Fin 3))).val + 1), by omega⟩ := by
        rw [hblockB]
        apply congrArg eB
        apply Fin.ext
        simp [finProdFinEquiv]
        omega
      rw [h0, h1]
      exact h
    · have hi : (finProdFinEquiv (b, (1 : Fin 3))).val + 1 < kB * 3 := by
        simp [finProdFinEquiv]
        omega
      have h := cycleB ⟨(finProdFinEquiv (b, (1 : Fin 3))).val, by omega⟩
      have h1 : blockB (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))) =
          eB ⟨2 + (finProdFinEquiv (b, (1 : Fin 3))).val, by omega⟩ := by
        rw [hblockB]
        apply congrArg eB
        apply Fin.ext
        rfl
      have h2 : blockB (Sum.inl (finProdFinEquiv (b, (2 : Fin 3)))) =
          eB ⟨2 + ((finProdFinEquiv (b, (1 : Fin 3))).val + 1), by omega⟩ := by
        rw [hblockB]
        apply congrArg eB
        apply Fin.ext
        simp [finProdFinEquiv]
        omega
      rw [h1, h2]
      exact h
  have hcross01 : G.Adj (Sum.inl (blockA (Sum.inr (0 : Fin 1))))
      (Sum.inr (blockB (Sum.inr (0 : Fin 2)))) := by
    rw [hblockA0, hblockB0]
    exact cross01
  have hcross12 : G.Adj (Sum.inr (blockB (Sum.inr (0 : Fin 2))))
      (Sum.inr (blockB (Sum.inr (1 : Fin 2)))) := by
    rw [hblockB0, hblockB1]
    exact cross12
  exact R03SP01ThreePieceCrossAssembly G kA kB blockA blockB hA hB hcross01 hcross12

#print axioms R03SP01TwoCycleResidueAssembly

/-- The same residue construction with actual cyclic successor hypotheses.
    The cyclic wrap edges are stronger than needed for the residual tiling, but
    make the two-cycle interpretation explicit. -/
theorem R03SP01TwoCycleCyclicOrderAssembly
    {A B : Type u} [Fintype A] [Fintype B]
    (G : SimpleGraph (A ⊕ B))
    (kA kB : Nat)
    (eA : Fin (1 + kA * 3) ≃ A)
    (eB : Fin (2 + kB * 3) ≃ B)
    (cycleA : ∀ i : Fin (1 + kA * 3),
      G.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨(i.val + 1) % (1 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (cycleB : ∀ i : Fin (2 + kB * 3),
      G.Adj (Sum.inr (eB i))
        (Sum.inr (eB ⟨(i.val + 1) % (2 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (cross01 : G.Adj (Sum.inl (eA 0)) (Sum.inr (eB 0)))
    (cross12 : G.Adj (Sum.inr (eB 0)) (Sum.inr (eB 1))) :
    Nonempty (P3Factor G) := by
  have pathA : ∀ i : Fin (kA * 3 - 1),
      G.Adj (Sum.inl (eA ⟨1 + i.val, by omega⟩))
        (Sum.inl (eA ⟨1 + (i.val + 1), by omega⟩)) := by
    intro i
    have hi := i.is_lt
    have h := cycleA ⟨1 + i.val, by omega⟩
    have hs :
        (⟨((1 + i.val) + 1) % (1 + kA * 3),
          Nat.mod_lt _ (by omega)⟩ : Fin (1 + kA * 3)) =
          ⟨1 + (i.val + 1), by omega⟩ := by
      apply Fin.ext
      calc
        ((1 + i.val) + 1) % (1 + kA * 3) = (1 + i.val) + 1 :=
          Nat.mod_eq_of_lt (by omega)
        _ = 1 + (i.val + 1) := by omega
    rw [hs] at h
    exact h
  have pathB : ∀ i : Fin (kB * 3 - 1),
      G.Adj (Sum.inr (eB ⟨2 + i.val, by omega⟩))
        (Sum.inr (eB ⟨2 + (i.val + 1), by omega⟩)) := by
    intro i
    have hi := i.is_lt
    have h := cycleB ⟨2 + i.val, by omega⟩
    have hs :
        (⟨((2 + i.val) + 1) % (2 + kB * 3),
          Nat.mod_lt _ (by omega)⟩ : Fin (2 + kB * 3)) =
          ⟨2 + (i.val + 1), by omega⟩ := by
      apply Fin.ext
      calc
        ((2 + i.val) + 1) % (2 + kB * 3) = (2 + i.val) + 1 :=
          Nat.mod_eq_of_lt (by omega)
        _ = 2 + (i.val + 1) := by omega
    rw [hs] at h
    exact h
  exact R03SP01TwoCycleResidueAssembly G kA kB eA eB pathA pathB cross01 cross12

#print axioms R03SP01TwoCycleCyclicOrderAssembly

/-- Symmetric residue orientation: the order-2 side is named first. -/
theorem R03SP01TwoCycleCyclicOrderAssemblySwap
    {A B : Type u} [Fintype A] [Fintype B]
    (G : SimpleGraph (A ⊕ B))
    (kA kB : Nat)
    (eA : Fin (2 + kA * 3) ≃ A)
    (eB : Fin (1 + kB * 3) ≃ B)
    (cycleA : ∀ i : Fin (2 + kA * 3),
      G.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨(i.val + 1) % (2 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (cycleB : ∀ i : Fin (1 + kB * 3),
      G.Adj (Sum.inr (eB i))
        (Sum.inr (eB ⟨(i.val + 1) % (1 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (cross01 : G.Adj (Sum.inl (eA 0)) (Sum.inr (eB 0)))
    (cross12 : G.Adj (Sum.inl (eA 0)) (Sum.inl (eA 1))) :
    Nonempty (P3Factor G) := by
  let Gswap : SimpleGraph (B ⊕ A) := G.comap (Equiv.sumComm B A)
  have hcycleA : ∀ i : Fin (1 + kB * 3),
      Gswap.Adj (Sum.inl (eB i))
        (Sum.inl (eB ⟨(i.val + 1) % (1 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    intro i
    simpa [Gswap] using cycleB i
  have hcycleB : ∀ i : Fin (2 + kA * 3),
      Gswap.Adj (Sum.inr (eA i))
        (Sum.inr (eA ⟨(i.val + 1) % (2 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    intro i
    simpa [Gswap] using cycleA i
  have hcross01 : Gswap.Adj (Sum.inl (eB 0)) (Sum.inr (eA 0)) := by
    simpa [Gswap] using cross01.symm
  have hcross12 : Gswap.Adj (Sum.inr (eA 0)) (Sum.inr (eA 1)) := by
    simpa [Gswap] using cross12
  obtain ⟨p⟩ := R03SP01TwoCycleCyclicOrderAssembly
    Gswap kB kA eB eA hcycleA hcycleB hcross01 hcross12
  let swap : (B ⊕ A) ≃ (A ⊕ B) := Equiv.sumComm B A
  refine ⟨{
    blockCount := p.blockCount
    place := p.place.trans swap
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    have h := p.edge01 i
    simpa [Gswap, swap] using h
  · intro i
    have h := p.edge12 i
    simpa [Gswap, swap] using h

#print axioms R03SP01TwoCycleCyclicOrderAssemblySwap

/-- A walk crossing from the first summand to the second contains a cross edge. -/
theorem R03SP01ExistsCrossEdgeOfConnected
    {A B : Type u} (G : SimpleGraph (A ⊕ B))
    (a0 : A) (b0 : B) (hconn : G.Connected) :
    ∃ a : A, ∃ b : B, G.Adj (Sum.inl a) (Sum.inr b) := by
  let rec walkCross (a : A) (b : B) (p : G.Walk (Sum.inl a) (Sum.inr b)) :
      ∃ a' : A, ∃ b' : B, G.Adj (Sum.inl a') (Sum.inr b') := by
    obtain ⟨w, h, q, hpq⟩ := Walk.exists_eq_cons_of_ne (by simp) p
    cases w with
    | inl a' => exact walkCross a' b q
    | inr b' => exact ⟨a, b', h⟩
  termination_by p.length
  decreasing_by
    simp_all [Walk.length_cons]
  obtain ⟨hp⟩ := hconn (Sum.inl a0) (Sum.inr b0)
  exact walkCross _ _ hp

/-- Cyclic successor edges are preserved by shifting the chosen origin. -/
theorem R03SP01ShiftCyclicOrder
    {X : Type u} {n : Nat} (R : X → X → Prop)
    (e : Fin n ≃ X) (hn : 0 < n)
    (cycle : ∀ i : Fin n, R (e i)
      (e ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩))
    (s : Fin n) :
    ∀ i : Fin n, R ((finCycle s).trans e i)
      (((finCycle s).trans e) ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  intro i
  have h := cycle (finCycle s i)
  have hi : (⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = i + 1 := by
    ext
    simp [Fin.val_add]
  have hs : finCycle s (i + 1) = finCycle s i + 1 := by
    ext
    simp [finCycle_apply, Fin.add_def]
    ac_rfl
  have hsucc (j : Fin n) :
      (⟨(j.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = j + 1 := by
    ext
    simp [Fin.val_add]
  rw [hsucc (finCycle s i)] at h
  simpa [Equiv.trans_apply, hi, hs] using h

/-- Connectedness supplies the exceptional cross edge after cyclic origins are shifted. -/
theorem R03SP01TwoCycleCyclicOrderAssemblyConnected
    {A B : Type u} [Fintype A] [Fintype B]
    (G : SimpleGraph (A ⊕ B))
    (kA kB : Nat)
    (eA : Fin (1 + kA * 3) ≃ A)
    (eB : Fin (2 + kB * 3) ≃ B)
    (cycleA : ∀ i : Fin (1 + kA * 3),
      G.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨(i.val + 1) % (1 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (cycleB : ∀ i : Fin (2 + kB * 3),
      G.Adj (Sum.inr (eB i))
        (Sum.inr (eB ⟨(i.val + 1) % (2 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (hconn : G.Connected) :
    Nonempty (P3Factor G) := by
  obtain ⟨a, b, hab⟩ := R03SP01ExistsCrossEdgeOfConnected
    G (eA 0) (eB 0) hconn
  let sA : Fin (1 + kA * 3) := eA.symm a
  let sB : Fin (2 + kB * 3) := eB.symm b
  letI : NeZero (1 + kA * 3) := ⟨by omega⟩
  letI : NeZero (2 + kB * 3) := ⟨by omega⟩
  let eA' : Fin (1 + kA * 3) ≃ A := (finCycle sA).trans eA
  let eB' : Fin (2 + kB * 3) ≃ B := (finCycle sB).trans eB
  have heA0 : eA' 0 = a := by
    simp [eA', sA]
  have heB0 : eB' 0 = b := by
    simp [eB', sB]
  have hcycleA' : ∀ i : Fin (1 + kA * 3),
      G.Adj (Sum.inl (eA' i))
        (Sum.inl (eA' ⟨(i.val + 1) % (1 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    simpa [eA'] using R03SP01ShiftCyclicOrder
      (fun x y => G.Adj (Sum.inl x) (Sum.inl y)) eA (by omega) cycleA sA
  have hcycleB' : ∀ i : Fin (2 + kB * 3),
      G.Adj (Sum.inr (eB' i))
        (Sum.inr (eB' ⟨(i.val + 1) % (2 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    simpa [eB'] using R03SP01ShiftCyclicOrder
      (fun x y => G.Adj (Sum.inr x) (Sum.inr y)) eB (by omega) cycleB sB
  have hcross01' : G.Adj (Sum.inl (eA' 0)) (Sum.inr (eB' 0)) := by
    rw [heA0, heB0]
    exact hab
  have hcross12' : G.Adj (Sum.inr (eB' 0)) (Sum.inr (eB' 1)) := by
    have h := hcycleB' 0
    have hnext : (⟨((0 : Fin (2 + kB * 3)).val + 1) % (2 + kB * 3),
        Nat.mod_lt _ (by omega)⟩ : Fin (2 + kB * 3)) = 1 := by
      ext
      simp
    rw [hnext] at h
    exact h
  exact R03SP01TwoCycleCyclicOrderAssembly
    G kA kB eA' eB' hcycleA' hcycleB' hcross01' hcross12'

#print axioms R03SP01ExistsCrossEdgeOfConnected
#print axioms R03SP01ShiftCyclicOrder
#print axioms R03SP01TwoCycleCyclicOrderAssemblyConnected

/-- Connectedness version with the order-2 residue on the first summand. -/
theorem R03SP01TwoCycleCyclicOrderAssemblyConnectedSwap
    {A B : Type u} [Fintype A] [Fintype B]
    (G : SimpleGraph (A ⊕ B))
    (kA kB : Nat)
    (eA : Fin (2 + kA * 3) ≃ A)
    (eB : Fin (1 + kB * 3) ≃ B)
    (cycleA : ∀ i : Fin (2 + kA * 3),
      G.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨(i.val + 1) % (2 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (cycleB : ∀ i : Fin (1 + kB * 3),
      G.Adj (Sum.inr (eB i))
        (Sum.inr (eB ⟨(i.val + 1) % (1 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (hconn : G.Connected) :
    Nonempty (P3Factor G) := by
  obtain ⟨a, b, hab⟩ := R03SP01ExistsCrossEdgeOfConnected
    G (eA 0) (eB 0) hconn
  let sA : Fin (2 + kA * 3) := eA.symm a
  let sB : Fin (1 + kB * 3) := eB.symm b
  letI : NeZero (2 + kA * 3) := ⟨by omega⟩
  letI : NeZero (1 + kB * 3) := ⟨by omega⟩
  let eA' : Fin (2 + kA * 3) ≃ A := (finCycle sA).trans eA
  let eB' : Fin (1 + kB * 3) ≃ B := (finCycle sB).trans eB
  have heA0 : eA' 0 = a := by
    simp [eA', sA]
  have heB0 : eB' 0 = b := by
    simp [eB', sB]
  have hcycleA' : ∀ i : Fin (2 + kA * 3),
      G.Adj (Sum.inl (eA' i))
        (Sum.inl (eA' ⟨(i.val + 1) % (2 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    simpa [eA'] using R03SP01ShiftCyclicOrder
      (fun x y => G.Adj (Sum.inl x) (Sum.inl y)) eA (by omega) cycleA sA
  have hcycleB' : ∀ i : Fin (1 + kB * 3),
      G.Adj (Sum.inr (eB' i))
        (Sum.inr (eB' ⟨(i.val + 1) % (1 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    simpa [eB'] using R03SP01ShiftCyclicOrder
      (fun x y => G.Adj (Sum.inr x) (Sum.inr y)) eB (by omega) cycleB sB
  have hcross01' : G.Adj (Sum.inl (eA' 0)) (Sum.inr (eB' 0)) := by
    rw [heA0, heB0]
    exact hab
  have hcross12' : G.Adj (Sum.inl (eA' 0)) (Sum.inl (eA' 1)) := by
    have h := hcycleA' 0
    have hnext : (⟨((0 : Fin (2 + kA * 3)).val + 1) % (2 + kA * 3),
        Nat.mod_lt _ (by omega)⟩ : Fin (2 + kA * 3)) = 1 := by
      ext
      simp
    rw [hnext] at h
    exact h
  exact R03SP01TwoCycleCyclicOrderAssemblySwap
    G kA kB eA' eB' hcycleA' hcycleB' hcross01' hcross12'

#print axioms R03SP01TwoCycleCyclicOrderAssemblyConnectedSwap

/-- Two-cycle assembly from a supplied cross edge, without requiring ambient
connectedness. The cyclic origins are shifted to the edge endpoints. -/
theorem R03SP01TwoCycleCyclicOrderAssemblyAtCross
    {A B : Type u} [Fintype A] [Fintype B]
    (G : SimpleGraph (A ⊕ B))
    (kA kB : Nat)
    (eA : Fin (1 + kA * 3) ≃ A)
    (eB : Fin (2 + kB * 3) ≃ B)
    (cycleA : ∀ i : Fin (1 + kA * 3),
      G.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨(i.val + 1) % (1 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (cycleB : ∀ i : Fin (2 + kB * 3),
      G.Adj (Sum.inr (eB i))
        (Sum.inr (eB ⟨(i.val + 1) % (2 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (iA : Fin (1 + kA * 3)) (iB : Fin (2 + kB * 3))
    (cross : G.Adj (Sum.inl (eA iA)) (Sum.inr (eB iB))) :
    Nonempty (P3Factor G) := by
  letI : NeZero (1 + kA * 3) := ⟨by omega⟩
  letI : NeZero (2 + kB * 3) := ⟨by omega⟩
  let eA' : Fin (1 + kA * 3) ≃ A := (finCycle iA).trans eA
  let eB' : Fin (2 + kB * 3) ≃ B := (finCycle iB).trans eB
  have heA0 : eA' 0 = eA iA := by simp [eA']
  have heB0 : eB' 0 = eB iB := by simp [eB']
  have hcycleA' : ∀ i : Fin (1 + kA * 3),
      G.Adj (Sum.inl (eA' i))
        (Sum.inl (eA' ⟨(i.val + 1) % (1 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    simpa [eA'] using R03SP01ShiftCyclicOrder
      (fun x y => G.Adj (Sum.inl x) (Sum.inl y)) eA (by omega) cycleA iA
  have hcycleB' : ∀ i : Fin (2 + kB * 3),
      G.Adj (Sum.inr (eB' i))
        (Sum.inr (eB' ⟨(i.val + 1) % (2 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    simpa [eB'] using R03SP01ShiftCyclicOrder
      (fun x y => G.Adj (Sum.inr x) (Sum.inr y)) eB (by omega) cycleB iB
  have hcross01' : G.Adj (Sum.inl (eA' 0)) (Sum.inr (eB' 0)) := by
    rw [heA0, heB0]
    exact cross
  have hcross12' : G.Adj (Sum.inr (eB' 0)) (Sum.inr (eB' 1)) := by
    have h := hcycleB' 0
    have hnext : (⟨((0 : Fin (2 + kB * 3)).val + 1) % (2 + kB * 3),
        Nat.mod_lt _ (by omega)⟩ : Fin (2 + kB * 3)) = 1 := by
      ext
      simp
    rw [hnext] at h
    exact h
  exact R03SP01TwoCycleCyclicOrderAssembly
    G kA kB eA' eB' hcycleA' hcycleB' hcross01' hcross12'

/-- Symmetric supplied-cross-edge form with the order-2 residue on the first
summand. -/
theorem R03SP01TwoCycleCyclicOrderAssemblyAtCrossSwap
    {A B : Type u} [Fintype A] [Fintype B]
    (G : SimpleGraph (A ⊕ B))
    (kA kB : Nat)
    (eA : Fin (2 + kA * 3) ≃ A)
    (eB : Fin (1 + kB * 3) ≃ B)
    (cycleA : ∀ i : Fin (2 + kA * 3),
      G.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨(i.val + 1) % (2 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (cycleB : ∀ i : Fin (1 + kB * 3),
      G.Adj (Sum.inr (eB i))
        (Sum.inr (eB ⟨(i.val + 1) % (1 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (iA : Fin (2 + kA * 3)) (iB : Fin (1 + kB * 3))
    (cross : G.Adj (Sum.inl (eA iA)) (Sum.inr (eB iB))) :
    Nonempty (P3Factor G) := by
  letI : NeZero (2 + kA * 3) := ⟨by omega⟩
  letI : NeZero (1 + kB * 3) := ⟨by omega⟩
  let eA' : Fin (2 + kA * 3) ≃ A := (finCycle iA).trans eA
  let eB' : Fin (1 + kB * 3) ≃ B := (finCycle iB).trans eB
  have heA0 : eA' 0 = eA iA := by simp [eA']
  have heB0 : eB' 0 = eB iB := by simp [eB']
  have hcycleA' : ∀ i : Fin (2 + kA * 3),
      G.Adj (Sum.inl (eA' i))
        (Sum.inl (eA' ⟨(i.val + 1) % (2 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    simpa [eA'] using R03SP01ShiftCyclicOrder
      (fun x y => G.Adj (Sum.inl x) (Sum.inl y)) eA (by omega) cycleA iA
  have hcycleB' : ∀ i : Fin (1 + kB * 3),
      G.Adj (Sum.inr (eB' i))
        (Sum.inr (eB' ⟨(i.val + 1) % (1 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    simpa [eB'] using R03SP01ShiftCyclicOrder
      (fun x y => G.Adj (Sum.inr x) (Sum.inr y)) eB (by omega) cycleB iB
  have hcross01' : G.Adj (Sum.inl (eA' 0)) (Sum.inr (eB' 0)) := by
    rw [heA0, heB0]
    exact cross
  have hcross12' : G.Adj (Sum.inl (eA' 0)) (Sum.inl (eA' 1)) := by
    have h := hcycleA' 0
    have hnext : (⟨((0 : Fin (2 + kA * 3)).val + 1) % (2 + kA * 3),
        Nat.mod_lt _ (by omega)⟩ : Fin (2 + kA * 3)) = 1 := by
      ext
      simp
    rw [hnext] at h
    exact h
  exact R03SP01TwoCycleCyclicOrderAssemblySwap
    G kA kB eA' eB' hcycleA' hcycleB' hcross01' hcross12'

#print axioms R03SP01TwoCycleCyclicOrderAssemblyAtCross
#print axioms R03SP01TwoCycleCyclicOrderAssemblyAtCrossSwap

theorem R03SP01CycleOrderOfIsCyclesComponent
    {V : Type u} [Fintype V]
    (F : SimpleGraph V)
    (hcycles : F.IsCycles)
    (h2 : ∀ v : V, Nat.card {w : V // F.Adj v w} = 2)
    (c : F.ConnectedComponent) (n : Nat) [Fintype c.supp]
    (hn : 0 < n)
    (hcard : Fintype.card c.supp = n) :
    ∃ e : Fin n ≃ c.supp, ∀ i : Fin n,
      F.Adj (e i : V)
        (e ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : V) := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨v, hv⟩ := c.nonempty_supp
  have hvne : (F.neighborSet v).Nonempty := by
    have hcardv : (F.neighborSet v).ncard = 2 := by
      change Nat.card {w : V // F.Adj v w} = 2
      exact h2 v
    exact Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨p, hp, hpverts⟩ :=
    hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv hvne
  have hpne : ¬ p.Nil := hp.not_nil
  let q := p.tail
  have hqnodup : q.support.Nodup := by
    rw [show q.support = p.support.tail by
      dsimp [q]
      exact p.support_tail_of_not_nil hpne]
    exact hp.support_nodup
  have hqset : {x : V | x ∈ q.support} = c.supp := by
    ext x
    constructor
    · intro hx
      have hxps : x ∈ p.support := by
        rw [p.mem_support_iff]
        right
        have hxq : x ∈ p.tail.support := by
          change x ∈ q.support at hx
          exact hx
        rw [p.support_tail_of_not_nil hpne] at hxq
        exact hxq
      rw [← hpverts]
      exact (p.mem_verts_toSubgraph).2 hxps
    · intro hx
      have hxverts : x ∈ p.toSubgraph.verts := hpverts ▸ hx
      have hxps : x ∈ p.support := (p.mem_verts_toSubgraph).1 hxverts
      rw [p.mem_support_iff] at hxps
      rcases hxps with rfl | hxt
      · change x ∈ p.tail.support
        rw [p.support_tail_of_not_nil hpne]
        exact p.end_mem_tail_support hpne
      · change x ∈ p.tail.support
        rw [p.support_tail_of_not_nil hpne]
        exact hxt
  let eList : Fin q.support.length ≃ {x : V // x ∈ q.support} :=
    List.Nodup.getEquiv q.support hqnodup
  let eSet : {x : V // x ∈ q.support} ≃ c.supp := Equiv.setCongr hqset
  have hlen : q.support.length = n := by
    calc
      q.support.length = Fintype.card {x : V // x ∈ q.support} := by
        symm
        simpa using (Fintype.card_congr eList).symm
      _ = Fintype.card c.supp := Fintype.card_congr eSet
      _ = n := hcard
  let e : Fin n ≃ c.supp :=
    (finCongr hlen.symm).trans (eList.trans eSet)
  refine ⟨e, ?_⟩
  intro i
  have he (j : Fin n) : (e j : V) = q.getVert (j : Nat) := by
    dsimp [e, eSet, eList]
    change q.support.get (finCongr hlen.symm j) = _
    rw [← q.getVert_comp_val_eq_get_support]
    rfl
  rw [he i]
  by_cases hi : (i : Nat) < q.length
  · have hadj := q.adj_getVert_succ hi
    have hin : i.val + 1 < n := by
      have hi' : i.val < q.support.length := by rw [hlen]; exact i.isLt
      have hlenq : q.length + 1 = n := q.length_support.symm.trans hlen
      rw [q.length_support] at hi'
      omega
    have hnext : (⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) =
        ⟨i.val + 1, by omega⟩ := by
      ext
      exact Nat.mod_eq_of_lt hin
    rw [hnext, he]
    exact hadj
  · have hilast : (i : Nat) = q.length := by
      have hqplus : q.support.length = q.length + 1 := q.length_support
      have hilt : (i : Nat) < q.support.length := by rw [hlen]; exact i.isLt
      omega
    have hqend : q.getVert q.length = p.getVert p.length := by
      simp only [q, SimpleGraph.Walk.getVert_tail]
      rw [p.length_tail_add_one hpne]
    have hqstart : q.getVert 0 = p.snd := by
      simp [q]
    have hadj : F.Adj (q.getVert q.length) (q.getVert 0) := by
      rw [hqend, hqstart, p.getVert_length]
      exact p.adj_snd hpne
    have hnlen : n = q.length + 1 := by
      calc
        n = q.support.length := hlen.symm
        _ = q.length + 1 := q.length_support
    have hnext : (⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = 0 := by
      apply Fin.ext
      simp only [Fin.val_zero]
      rw [hilast]
      apply Nat.mod_eq_zero_of_dvd
      rw [hnlen]
    have hfirst : q.getVert (i : Nat) = q.getVert q.length := by
      rw [hilast]
    rw [hfirst, hnext, he]
    exact hadj


theorem R03SP01TwoFactorTwoCycleP3Factor
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    (cA cB : F.ConnectedComponent)
    (eV : cA.supp ⊕ cB.supp ≃ V)
    (heV_inl : ∀ x : cA.supp, eV (Sum.inl x) = x.1)
    (heV_inr : ∀ x : cB.supp, eV (Sum.inr x) = x.1)
    (kA kB : Nat)
    [Fintype cA.supp] [Fintype cB.supp]
    (hcardA : Fintype.card cA.supp = 1 + kA * 3)
    (hcardB : Fintype.card cB.supp = 2 + kB * 3)
    (hconn : G.Connected) :
    Nonempty (P3Factor G) := by
  classical
  have hcycles : F.IsCycles := by
    intro v hv
    change Nat.card {w : V // F.Adj v w} = 2
    exact hTF.2 v
  have h2 : ∀ v : V, Nat.card {w : V // F.Adj v w} = 2 := fun v => by
    exact hTF.2 v
  obtain ⟨eA, hcyA⟩ := R03SP01CycleOrderOfIsCyclesComponent
    F hcycles h2 cA (1 + kA * 3) (by omega) hcardA
  obtain ⟨eB, hcyB⟩ := R03SP01CycleOrderOfIsCyclesComponent
    F hcycles h2 cB (2 + kB * 3) (by omega) hcardB
  let Gsum : SimpleGraph (cA.supp ⊕ cB.supp) := G.comap eV
  have hsumconn : Gsum.Connected := by
    apply (SimpleGraph.Iso.comap eV G).connected_iff.mpr hconn
  have hcycleA : ∀ i : Fin (1 + kA * 3),
      Gsum.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨(i.val + 1) % (1 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    intro i
    have hf := hcyA i
    have hg := hTF.1 hf
    simpa [Gsum, heV_inl] using hg
  have hcycleB : ∀ i : Fin (2 + kB * 3),
      Gsum.Adj (Sum.inr (eB i))
        (Sum.inr (eB ⟨(i.val + 1) % (2 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    intro i
    have hf := hcyB i
    have hg := hTF.1 hf
    simpa [Gsum, heV_inr] using hg
  obtain ⟨p⟩ := R03SP01TwoCycleCyclicOrderAssemblyConnected
    Gsum kA kB eA eB hcycleA hcycleB hsumconn
  refine ⟨{
    blockCount := p.blockCount
    place := p.place.trans eV
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    exact p.edge01 i
  · intro i
    exact p.edge12 i

#print axioms R03SP01CycleOrderOfIsCyclesComponent
#print axioms R03SP01TwoFactorTwoCycleP3Factor

/-- The support sum of two distinct connected components is equivalent to the
whole vertex type when the two supports cover it. -/
theorem R03SP01TwoComponentSupportEquiv
    {V : Type u} [Fintype V]
    (F : SimpleGraph V)
    (cA cB : F.ConnectedComponent)
    (hneq : cA ≠ cB)
    (hcover : ∀ v : V, v ∈ cA.supp ∨ v ∈ cB.supp) :
    ∃ (eV : cA.supp ⊕ cB.supp ≃ V),
      (∀ x : cA.supp, eV (Sum.inl x) = x.1) ∧
      (∀ x : cB.supp, eV (Sum.inr x) = x.1) := by
  classical
  have hdisj : Disjoint cA.supp cB.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent F) hneq
  let eVFun : cA.supp ⊕ cB.supp → V := fun z =>
    match z with
    | Sum.inl x => x.1
    | Sum.inr x => x.1
  have hinj : Function.Injective eVFun := by
    intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        apply congrArg Sum.inl
        apply Subtype.ext
        exact hxy
      | inr y =>
        exfalso
        change x.1 = y.1 at hxy
        apply (Set.disjoint_left.mp hdisj) x.2
        simpa [hxy] using y.2
    | inr x =>
      cases y with
      | inl y =>
        exfalso
        change x.1 = y.1 at hxy
        apply (Set.disjoint_left.mp hdisj) y.2
        simpa [hxy] using x.2
      | inr y =>
        apply congrArg Sum.inr
        apply Subtype.ext
        exact hxy
  have hsurj : Function.Surjective eVFun := by
    intro v
    rcases hcover v with hv | hv
    · exact ⟨Sum.inl ⟨v, hv⟩, rfl⟩
    · exact ⟨Sum.inr ⟨v, hv⟩, rfl⟩
  let eV : cA.supp ⊕ cB.supp ≃ V := Equiv.ofBijective eVFun ⟨hinj, hsurj⟩
  refine ⟨eV, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rfl

/-- Two-cycle bridge with the component-cover hypothesis rather than an
externally supplied support equivalence. -/
theorem R03SP01TwoFactorTwoCycleP3FactorOfCover
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    (cA cB : F.ConnectedComponent)
    (hneq : cA ≠ cB)
    (hcover : ∀ v : V, v ∈ cA.supp ∨ v ∈ cB.supp)
    (kA kB : Nat)
    [Fintype cA.supp] [Fintype cB.supp]
    (hcardA : Fintype.card cA.supp = 1 + kA * 3)
    (hcardB : Fintype.card cB.supp = 2 + kB * 3)
    (hconn : G.Connected) :
    Nonempty (P3Factor G) := by
  obtain ⟨eV, heV_inl, heV_inr⟩ := R03SP01TwoComponentSupportEquiv
    F cA cB hneq hcover
  exact R03SP01TwoFactorTwoCycleP3Factor G F hTF cA cB eV
    heV_inl heV_inr kA kB hcardA hcardB hconn

#print axioms R03SP01TwoComponentSupportEquiv
#print axioms R03SP01TwoFactorTwoCycleP3FactorOfCover

/-- The same component-cover bridge with the two nonzero residues reversed. -/
theorem R03SP01TwoFactorTwoCycleP3FactorOfCoverSwap
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    (cA cB : F.ConnectedComponent)
    (hneq : cA ≠ cB)
    (hcover : ∀ v : V, v ∈ cA.supp ∨ v ∈ cB.supp)
    (kA kB : Nat)
    [Fintype cA.supp] [Fintype cB.supp]
    (hcardA : Fintype.card cA.supp = 2 + kA * 3)
    (hcardB : Fintype.card cB.supp = 1 + kB * 3)
    (hconn : G.Connected) :
    Nonempty (P3Factor G) := by
  obtain ⟨eV, heV_inl, heV_inr⟩ := R03SP01TwoComponentSupportEquiv
    F cB cA hneq.symm (fun v =>
      (hcover v).elim (fun hv => Or.inr hv) (fun hv => Or.inl hv))
  exact R03SP01TwoFactorTwoCycleP3Factor G F hTF cB cA eV
    heV_inl heV_inr kB kA hcardB hcardA hconn

#print axioms R03SP01TwoFactorTwoCycleP3FactorOfCoverSwap

/-- The nonzero-residue two-component case can use only total-order
 divisibility; the arithmetic branch excludes the already-covered zero-zero
 profile. -/
theorem R03SP01TwoFactorTwoCycleNonzeroOfDivisibleOrder
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    (cA cB : F.ConnectedComponent)
    (hneq : cA ≠ cB)
    (hcover : ∀ v : V, v ∈ cA.supp ∨ v ∈ cB.supp)
    [Fintype cA.supp] [Fintype cB.supp]
    (horder : 3 ∣ Fintype.card V)
    (hnotzero : ¬(3 ∣ Fintype.card cA.supp ∧ 3 ∣ Fintype.card cB.supp))
    (hconn : G.Connected) :
    Nonempty (P3Factor G) := by
  obtain ⟨eV, _, _⟩ := R03SP01TwoComponentSupportEquiv
    F cA cB hneq hcover
  have hcardV : Fintype.card V = Fintype.card cA.supp + Fintype.card cB.supp := by
    calc
      Fintype.card V = Fintype.card (cA.supp ⊕ cB.supp) := by
        exact (Fintype.card_congr eV).symm
      _ = Fintype.card cA.supp + Fintype.card cB.supp := by simp
  have hsum : 3 ∣ Fintype.card cA.supp + Fintype.card cB.supp := by
    rw [← hcardV]
    exact horder
  have hclass :
      (∃ kA kB : Nat,
        Fintype.card cA.supp = kA * 3 ∧
        Fintype.card cB.supp = kB * 3) ∨
      (∃ kA kB : Nat,
        Fintype.card cA.supp = 1 + kA * 3 ∧
        Fintype.card cB.supp = 2 + kB * 3) ∨
      (∃ kA kB : Nat,
        Fintype.card cA.supp = 2 + kA * 3 ∧
        Fintype.card cB.supp = 1 + kB * 3) := by
    obtain ⟨q, hq⟩ := hsum
    have ha := Nat.mod_add_div (Fintype.card cA.supp) 3
    have hb := Nat.mod_add_div (Fintype.card cB.supp) 3
    have hla := Nat.mod_lt (Fintype.card cA.supp) (by omega : 0 < 3)
    have hlb := Nat.mod_lt (Fintype.card cB.supp) (by omega : 0 < 3)
    have hm : (Fintype.card cA.supp + Fintype.card cB.supp) % 3 = 0 := by
      rw [hq]
      simp
    have ham := Nat.add_mod (Fintype.card cA.supp) (Fintype.card cB.supp) 3
    by_cases ha0 : Fintype.card cA.supp % 3 = 0
    · by_cases hb0 : Fintype.card cB.supp % 3 = 0
      · left
        exact ⟨Fintype.card cA.supp / 3, Fintype.card cB.supp / 3,
          by omega, by omega⟩
      · by_cases hb1 : Fintype.card cB.supp % 3 = 1
        · exfalso
          omega
        · have hb2 : Fintype.card cB.supp % 3 = 2 := by omega
          exfalso
          omega
    · by_cases ha1 : Fintype.card cA.supp % 3 = 1
      · by_cases hb0 : Fintype.card cB.supp % 3 = 0
        · exfalso
          omega
        · by_cases hb1 : Fintype.card cB.supp % 3 = 1
          · exfalso
            omega
          · have hb2 : Fintype.card cB.supp % 3 = 2 := by omega
            right
            left
            exact ⟨Fintype.card cA.supp / 3, Fintype.card cB.supp / 3,
              by omega, by omega⟩
      · have ha2 : Fintype.card cA.supp % 3 = 2 := by omega
        by_cases hb0 : Fintype.card cB.supp % 3 = 0
        · exfalso
          omega
        · by_cases hb1 : Fintype.card cB.supp % 3 = 1
          · right
            right
            exact ⟨Fintype.card cA.supp / 3, Fintype.card cB.supp / 3,
              by omega, by omega⟩
          · have hb2 : Fintype.card cB.supp % 3 = 2 := by omega
            exfalso
            omega
  rcases hclass with hzero | hnonzero
  · obtain ⟨kA, kB, hcardA, hcardB⟩ := hzero
    apply False.elim
    apply hnotzero
    constructor
    · exact ⟨kA, by omega⟩
    · exact ⟨kB, by omega⟩
  · rcases hnonzero with hAB | hBA
    · obtain ⟨kA, kB, hcardA, hcardB⟩ := hAB
      exact R03SP01TwoFactorTwoCycleP3FactorOfCover G F hTF cA cB hneq
        hcover kA kB hcardA hcardB hconn
    · obtain ⟨kA, kB, hcardA, hcardB⟩ := hBA
      exact R03SP01TwoFactorTwoCycleP3FactorOfCoverSwap G F hTF cA cB hneq
        hcover kA kB hcardA hcardB hconn

#print axioms R03SP01TwoFactorTwoCycleNonzeroOfDivisibleOrder

/-- Component-cover bridge using one explicitly supplied cross edge between the
 two selected 2-factor components. This removes the ambient connectedness
 assumption from the two-cycle residue construction. -/
theorem R03SP01TwoFactorTwoCycleP3FactorOfCoverAtCross
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    (cA cB : F.ConnectedComponent)
    (hneq : cA ≠ cB)
    (hcover : ∀ v : V, v ∈ cA.supp ∨ v ∈ cB.supp)
    (xA xB : V)
    (hxA : xA ∈ cA.supp) (hxB : xB ∈ cB.supp)
    (hcross : G.Adj xA xB)
    (kA kB : Nat)
    [Fintype cA.supp] [Fintype cB.supp]
    (hcardA : Fintype.card cA.supp = 1 + kA * 3)
    (hcardB : Fintype.card cB.supp = 2 + kB * 3) :
    Nonempty (P3Factor G) := by
  classical
  obtain ⟨eV, heV_inl, heV_inr⟩ := R03SP01TwoComponentSupportEquiv
    F cA cB hneq hcover
  have hcycles : F.IsCycles := by
    intro v hv
    change Nat.card {w : V // F.Adj v w} = 2
    exact hTF.2 v
  have h2 : ∀ v : V, Nat.card {w : V // F.Adj v w} = 2 := fun v => by
    exact hTF.2 v
  obtain ⟨eA, hcyA⟩ := R03SP01CycleOrderOfIsCyclesComponent
    F hcycles h2 cA (1 + kA * 3) (by omega) hcardA
  obtain ⟨eB, hcyB⟩ := R03SP01CycleOrderOfIsCyclesComponent
    F hcycles h2 cB (2 + kB * 3) (by omega) hcardB
  let Gsum : SimpleGraph (cA.supp ⊕ cB.supp) := G.comap eV
  have hcycleA : ∀ i : Fin (1 + kA * 3),
      Gsum.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨(i.val + 1) % (1 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    intro i
    have hf := hcyA i
    have hg := hTF.1 hf
    simpa [Gsum, heV_inl] using hg
  have hcycleB : ∀ i : Fin (2 + kB * 3),
      Gsum.Adj (Sum.inr (eB i))
        (Sum.inr (eB ⟨(i.val + 1) % (2 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    intro i
    have hf := hcyB i
    have hg := hTF.1 hf
    simpa [Gsum, heV_inr] using hg
  let iA : Fin (1 + kA * 3) := eA.symm ⟨xA, hxA⟩
  let iB : Fin (2 + kB * 3) := eB.symm ⟨xB, hxB⟩
  have hcross' : Gsum.Adj (Sum.inl (eA iA)) (Sum.inr (eB iB)) := by
    simpa [Gsum, iA, iB, heV_inl, heV_inr] using hcross
  obtain ⟨p⟩ := R03SP01TwoCycleCyclicOrderAssemblyAtCross
    Gsum kA kB eA eB hcycleA hcycleB iA iB hcross'
  refine ⟨{
    blockCount := p.blockCount
    place := p.place.trans eV
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    exact p.edge01 i
  · intro i
    exact p.edge12 i

#print axioms R03SP01TwoFactorTwoCycleP3FactorOfCover

/-- Consecutive triples in an explicitly cyclically ordered multiple-of-three
set form a P3Factor. -/
theorem R03SP01CyclicDivisibleP3Factor
    {A : Type u} [Fintype A]
    (G : SimpleGraph A) (k : Nat) (hpos : 0 < k * 3)
    (e : Fin (k * 3) ≃ A)
    (cycle : ∀ i : Fin (k * 3),
      G.Adj (e i)
        (e ⟨(i.val + 1) % (k * 3), Nat.mod_lt _ hpos⟩)) :
    Nonempty (P3Factor G) := by
  refine ⟨{
    blockCount := k
    place := finProdFinEquiv.trans e
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    have h := cycle (finProdFinEquiv (i, (0 : Fin 3)))
    have hn : (k * 3) ≠ 0 := by omega
    have hidx : (⟨((finProdFinEquiv (i, (0 : Fin 3))).val + 1) % (k * 3),
        Nat.mod_lt _ hpos⟩ : Fin (k * 3)) = finProdFinEquiv (i, (1 : Fin 3)) := by
      apply Fin.ext
      dsimp [finProdFinEquiv]
      change (0 + 3 * i.val + 1) % (k * 3) = 1 + 3 * i.val
      simp only [zero_add]
      have hlt : 3 * i.val + 1 < k * 3 := by omega
      calc
        (3 * i.val + 1) % (k * 3) = 3 * i.val + 1 := Nat.mod_eq_of_lt hlt
        _ = 1 + 3 * i.val := by omega
    rw [hidx] at h
    exact h
  · intro i
    have h := cycle (finProdFinEquiv (i, (1 : Fin 3)))
    have hn : (k * 3) ≠ 0 := by omega
    have hidx : (⟨((finProdFinEquiv (i, (1 : Fin 3))).val + 1) % (k * 3),
        Nat.mod_lt _ hpos⟩ : Fin (k * 3)) = finProdFinEquiv (i, (2 : Fin 3)) := by
      apply Fin.ext
      dsimp [finProdFinEquiv]
      change (1 + 3 * i.val + 1) % (k * 3) = 2 + 3 * i.val
      have hlt : 1 + 3 * i.val + 1 < k * 3 := by omega
      calc
        (1 + 3 * i.val + 1) % (k * 3) = 1 + 3 * i.val + 1 := Nat.mod_eq_of_lt hlt
        _ = 2 + 3 * i.val := by omega
    rw [hidx] at h
    exact h

/-- Distribute a finite product over a binary sum. -/
def R03SP01SumProdDistrib {X Y Z : Type u} :
    ((X ⊕ Y) × Z) ≃ ((X × Z) ⊕ (Y × Z)) where
  toFun z := match z.1 with
    | Sum.inl x => Sum.inl (x, z.2)
    | Sum.inr y => Sum.inr (y, z.2)
  invFun z := match z with
    | Sum.inl x => (Sum.inl x.1, x.2)
    | Sum.inr y => (Sum.inr y.1, y.2)
  left_inv z := by cases z with | mk s z => cases s <;> rfl
  right_inv z := by cases z <;> rfl

/-- P3 factors on two disjoint vertex types glue into a factor on their sum. -/
theorem R03SP01P3FactorSum
    {A B : Type u} [Fintype A] [Fintype B]
    (GA : SimpleGraph A) (GB : SimpleGraph B)
    (G : SimpleGraph (A ⊕ B))
    (pA : P3Factor GA) (pB : P3Factor GB)
    (hA : ∀ {x y : A}, GA.Adj x y → G.Adj (Sum.inl x) (Sum.inl y))
    (hB : ∀ {x y : B}, GB.Adj x y → G.Adj (Sum.inr x) (Sum.inr y)) :
    Nonempty (P3Factor G) := by
  let blockEquiv : Fin (pA.blockCount + pB.blockCount) ≃
      Fin pA.blockCount ⊕ Fin pB.blockCount := finSumFinEquiv.symm
  let sourceEquiv : (Fin (pA.blockCount + pB.blockCount) × Fin 3) ≃
      ((Fin pA.blockCount × Fin 3) ⊕ (Fin pB.blockCount × Fin 3)) :=
    (blockEquiv.prodCongr (Equiv.refl (Fin 3))).trans R03SP01SumProdDistrib
  let placeEquiv : ((Fin pA.blockCount × Fin 3) ⊕
      (Fin pB.blockCount × Fin 3)) ≃ (A ⊕ B) :=
    Equiv.sumCongr pA.place pB.place
  let place : (Fin (pA.blockCount + pB.blockCount) × Fin 3) ≃ (A ⊕ B) :=
    sourceEquiv.trans placeEquiv
  refine ⟨{
    blockCount := pA.blockCount + pB.blockCount
    place := place
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    generalize hb : blockEquiv i = z
    cases z with
    | inl z =>
      have h := pA.edge01 z
      simpa [place, placeEquiv, sourceEquiv, R03SP01SumProdDistrib, hb] using hA h
    | inr z =>
      have h := pB.edge01 z
      simpa [place, placeEquiv, sourceEquiv, R03SP01SumProdDistrib, hb] using hB h
  · intro i
    generalize hb : blockEquiv i = z
    cases z with
    | inl z =>
      have h := pA.edge12 z
      simpa [place, placeEquiv, sourceEquiv, R03SP01SumProdDistrib, hb] using hA h
    | inr z =>
      have h := pB.edge12 z
      simpa [place, placeEquiv, sourceEquiv, R03SP01SumProdDistrib, hb] using hB h

#print axioms R03SP01CyclicDivisibleP3Factor
#print axioms R03SP01P3FactorSum

/-- The zero-zero residue profile of two cycle components is closed by
independent consecutive-triple tilings on each component and binary factor
sum gluing. -/
theorem R03SP01TwoFactorTwoCycleP3FactorZeroZero
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    (cA cB : F.ConnectedComponent)
    (hneq : cA ≠ cB)
    (hcover : ∀ v : V, v ∈ cA.supp ∨ v ∈ cB.supp)
    (kA kB : Nat)
    [Fintype cA.supp] [Fintype cB.supp]
    (hcardA : Fintype.card cA.supp = kA * 3)
    (hcardB : Fintype.card cB.supp = kB * 3) :
    Nonempty (P3Factor G) := by
  classical
  obtain ⟨eV, heV_inl, heV_inr⟩ := R03SP01TwoComponentSupportEquiv
    F cA cB hneq hcover
  have hcycles : F.IsCycles := by
    intro v hv
    change Nat.card {w : V // F.Adj v w} = 2
    exact hTF.2 v
  have h2 : ∀ v : V, Nat.card {w : V // F.Adj v w} = 2 := fun v => by
    exact hTF.2 v
  have hposA : 0 < Fintype.card cA.supp := by
    obtain ⟨v, hv⟩ := cA.nonempty_supp
    letI : Nonempty cA.supp := ⟨⟨v, hv⟩⟩
    exact Fintype.card_pos
  have hposB : 0 < Fintype.card cB.supp := by
    obtain ⟨v, hv⟩ := cB.nonempty_supp
    letI : Nonempty cB.supp := ⟨⟨v, hv⟩⟩
    exact Fintype.card_pos
  obtain ⟨eA, hcyA⟩ := R03SP01CycleOrderOfIsCyclesComponent
    F hcycles h2 cA (kA * 3) (by omega) hcardA
  obtain ⟨eB, hcyB⟩ := R03SP01CycleOrderOfIsCyclesComponent
    F hcycles h2 cB (kB * 3) (by omega) hcardB
  let GA : SimpleGraph cA.supp := G.induce cA.supp
  let GB : SimpleGraph cB.supp := G.induce cB.supp
  let Gsum : SimpleGraph (cA.supp ⊕ cB.supp) := G.comap eV
  have hGAcycle : ∀ i : Fin (kA * 3),
      GA.Adj (eA i)
        (eA ⟨(i.val + 1) % (kA * 3), Nat.mod_lt _ (by omega)⟩) := by
    intro i
    have hf := hcyA i
    have hg := hTF.1 hf
    simpa [GA] using hg
  have hGBcycle : ∀ i : Fin (kB * 3),
      GB.Adj (eB i)
        (eB ⟨(i.val + 1) % (kB * 3), Nat.mod_lt _ (by omega)⟩) := by
    intro i
    have hf := hcyB i
    have hg := hTF.1 hf
    simpa [GB] using hg
  obtain ⟨pA⟩ := R03SP01CyclicDivisibleP3Factor GA kA (by omega)
    eA hGAcycle
  obtain ⟨pB⟩ := R03SP01CyclicDivisibleP3Factor GB kB (by omega)
    eB hGBcycle
  have hA : ∀ {x y : cA.supp}, GA.Adj x y →
      Gsum.Adj (Sum.inl x) (Sum.inl y) := by
    intro x y hxy
    have hg : G.Adj x.1 y.1 := hxy
    simpa [Gsum, heV_inl] using hg
  have hB : ∀ {x y : cB.supp}, GB.Adj x y →
      Gsum.Adj (Sum.inr x) (Sum.inr y) := by
    intro x y hxy
    have hg : G.Adj x.1 y.1 := hxy
    simpa [Gsum, heV_inr] using hg
  obtain ⟨p⟩ := R03SP01P3FactorSum GA GB Gsum pA pB hA hB
  refine ⟨{
    blockCount := p.blockCount
    place := p.place.trans eV
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    exact p.edge01 i
  · intro i
    exact p.edge12 i

#print axioms R03SP01TwoFactorTwoCycleP3FactorZeroZero

/-- Exact-two-component closure: total-order divisibility selects either the
zero-zero tiling branch or the nonzero two-cycle cross-edge branch. -/
theorem R03SP01TwoFactorTwoCycleP3FactorOfDivisibleOrder
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    (cA cB : F.ConnectedComponent)
    (hneq : cA ≠ cB)
    (hcover : ∀ v : V, v ∈ cA.supp ∨ v ∈ cB.supp)
    [Fintype cA.supp] [Fintype cB.supp]
    (horder : 3 ∣ Fintype.card V)
    (hconn : G.Connected) :
    Nonempty (P3Factor G) := by
  by_cases hA : 3 ∣ Fintype.card cA.supp
  · by_cases hB : 3 ∣ Fintype.card cB.supp
    · obtain ⟨kA, hkA⟩ := hA
      obtain ⟨kB, hkB⟩ := hB
      exact R03SP01TwoFactorTwoCycleP3FactorZeroZero G F hTF cA cB
        hneq hcover kA kB (by omega) (by omega)
    · have hnotzero : ¬(3 ∣ Fintype.card cA.supp ∧
        3 ∣ Fintype.card cB.supp) := by
        intro h
        exact hB h.2
      exact R03SP01TwoFactorTwoCycleNonzeroOfDivisibleOrder
        G F hTF cA cB hneq hcover horder hnotzero hconn
  · have hnotzero : ¬(3 ∣ Fintype.card cA.supp ∧
      3 ∣ Fintype.card cB.supp) := by
      intro h
      exact hA h.1
    exact R03SP01TwoFactorTwoCycleNonzeroOfDivisibleOrder
      G F hTF cA cB hneq hcover horder hnotzero hconn

#print axioms R03SP01TwoFactorTwoCycleP3FactorOfDivisibleOrder
end CubicP3Partition

namespace R03CubicMatchingTwoCycleIntegration

open CubicP3Partition
open SimpleGraph

universe u

variable {V : Type u} [Fintype V]


end R03CubicMatchingTwoCycleIntegration

open R03CubicMatchingTwoCycleIntegration
open CubicP3Partition
open SimpleGraph
open scoped BigOperators
universe u
variable {V : Type u} [Fintype V]
theorem solution
    (G : SimpleGraph V)
    (hG : Cubic G) (hconn : ThreeVertexConnected G)
    (horder : 3 ∣ Fintype.card V)
    (hprofile : ∃ M : SimpleGraph V, PerfectMatching G M ∧
      ∃ cA cB : (matchingComplement G M).ConnectedComponent,
        cA ≠ cB ∧ (∀ v : V, v ∈ cA.supp ∨ v ∈ cB.supp)) :
    Nonempty (P3Factor G) := by
  let T : Set V := {v : V | v ∉ (∅ : Finset V)}
  let eV : (↥T) ≃ V := {
    toFun := fun x => x.1
    invFun := fun v => ⟨v, by simp [T]⟩
    left_inv := by intro x; apply Subtype.ext; rfl
    right_inv := by intro v; rfl }
  let eG : G.induce T ≃g G := {
    toFun := eV
    invFun := eV.symm
    left_inv := eV.left_inv
    right_inv := eV.right_inv
    map_rel_iff' := by
      intro x y
      simp [eV, T] }
  have hGconnected : G.Connected :=
    (SimpleGraph.Iso.connected_iff eG).mp
      (hconn.2 (∅ : Finset V) (by simp))
  obtain ⟨M, hM, cA, cB, hneq, hcover⟩ := hprofile
  let F : SimpleGraph V := matchingComplement G M
  have hTF : TwoFactor G F := by
    simpa [F] using
      R03PerfectMatchingCandidate.matchingComplement_twoFactor_of_cubic_perfectMatching_local
        hG hM
  letI : Fintype cA.supp := Fintype.ofFinite _
  letI : Fintype cB.supp := Fintype.ofFinite _
  exact R03SP01TwoFactorTwoCycleP3FactorOfDivisibleOrder
    G F hTF cA cB hneq hcover horder hGconnected

