-- Prove2me | solution 1 for R03PerfectMatchingCandidate.oddComponents_ncard_eq_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:54:44.168744+00:00
-- url     : https://prove2.me/submissions/0a3c93ff-ce50-44b1-86ca-1b4d5b162342

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


end R03PerfectMatchingCandidate

open R03PerfectMatchingCandidate
open CubicP3Partition
open SimpleGraph
open scoped BigOperators
universe u
variable {V : Type u} [Fintype V]
theorem solution {W : Type u} {X : Type u}
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

