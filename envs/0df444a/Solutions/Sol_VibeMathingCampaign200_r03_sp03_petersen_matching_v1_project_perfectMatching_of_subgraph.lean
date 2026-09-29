-- Prove2me | solution 1 for VibeMathingCampaign200.r03_sp03_petersen_matching_v1_project_perfectMatching_of_subgraph
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:48:25.594721+00:00
-- url     : https://prove2.me/submissions/42ded401-4d7f-4772-af81-f2f9efdc2119

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03SP03PetersenMatching

open CubicP3Partition
open scoped BigOperators

universe u

variable {V : Type u} [Fintype V]

noncomputable section

/-- The following helper packages the elementary parity fact used in the
bridgeless-cubic matching argument.  The involution is allowed to depend on
membership in the finite domain. -/
lemma even_card_of_fixedPointFree_involution_finset
    {α : Type u} (s : Finset α)
    (g : ∀ a ∈ s, α)
    (hmem : ∀ a ha, g a ha ∈ s)
    (hinv : ∀ a ha, g (g a ha) (hmem a ha) = a)
    (hfix : ∀ a ha, g a ha ≠ a) :
    Even s.card := by
  classical
  have hsum : ∑ a ∈ s, (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution g ?_ ?_ ?_ ?_
    · intro a ha
      decide
    · intro a ha hne
      exact hfix a ha
    · intro a ha
      exact hmem a ha
    · intro a ha
      exact hinv a ha
  have hsum' : (s.card : ZMod 2) = 0 := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum
  have hsum'' : ((s.card % 2 : Nat) : ZMod 2) = 0 := by
    rw [ZMod.natCast_mod]
    exact hsum'
  have hmod : s.card % 2 = 0 := by
    have hcases : s.card % 2 = 0 ∨ s.card % 2 = 1 := by omega
    rcases hcases with hzero | hone
    · exact hzero
    · exfalso
      rw [hone] at hsum''
      norm_num at hsum''
  exact (Nat.even_iff).2 hmod

section BoundaryDarts

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Oriented edges whose first endpoint lies in a finite vertex set. -/
def dartsFirst (G : SimpleGraph V) (S : Finset V) [DecidableRel G.Adj] : Finset G.Dart := by
  classical
  exact Finset.univ.filter (fun d => d.fst ∈ S)

/-- Oriented edges with both endpoints in a finite vertex set. -/
def dartsInternal (G : SimpleGraph V) (S : Finset V) [DecidableRel G.Adj] : Finset G.Dart := by
  classical
  exact Finset.univ.filter (fun d => d.fst ∈ S ∧ d.snd ∈ S)

/-- Oriented edges directed from a finite vertex set to its complement. -/
def dartsBoundary (G : SimpleGraph V) (S : Finset V) [DecidableRel G.Adj] : Finset G.Dart := by
  classical
  exact Finset.univ.filter (fun d => d.fst ∈ S ∧ d.snd ∉ S)

/-- Oriented edges whose second endpoint lies in a finite vertex set. -/
def dartsSecond (G : SimpleGraph V) (S : Finset V) [DecidableRel G.Adj] : Finset G.Dart := by
  classical
  exact Finset.univ.filter (fun d => d.snd ∈ S)

lemma card_dartsFirst_eq_sum_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    (dartsFirst G S).card = ∑ v ∈ S, G.degree v := by
  classical
  let e : {d : G.Dart // d.fst ∈ S} ≃ Σ v : S, G.neighborSet v := {
    toFun := fun d => ⟨⟨d.1.fst, d.2⟩, ⟨d.1.snd, d.1.adj⟩⟩
    invFun := fun x => ⟨⟨(x.1.1, x.2.1), x.2.2⟩, x.1.2⟩
    left_inv := by
      intro d
      apply Subtype.ext
      apply SimpleGraph.Dart.ext
      rfl
    right_inv := by
      intro x
      cases x with
      | mk x y => rfl
  }
  calc
    (dartsFirst G S).card = Fintype.card {d : G.Dart // d.fst ∈ S} := by
      exact (Fintype.card_ofFinset (dartsFirst G S) (by
        intro x
        simp only [dartsFirst, Finset.mem_filter, Finset.mem_univ, true_and]
        change x.fst ∈ S ↔ x.fst ∈ S
        rfl)).symm
    _ = Fintype.card (Σ v : S, G.neighborSet v) := Fintype.card_congr e
    _ = ∑ v : S, Fintype.card (G.neighborSet v) := Fintype.card_sigma
    _ = ∑ v ∈ S, Fintype.card (G.neighborSet v) := by
      exact Finset.sum_coe_sort S (fun v => Fintype.card (G.neighborSet v))
    _ = ∑ v ∈ S, G.degree v := by
      simp_rw [SimpleGraph.card_neighborSet_eq_degree]

lemma card_dartsSecond_eq_sum_degree (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] (S : Finset V) :
    (dartsSecond G S).card = ∑ v ∈ S, G.degree v := by
  classical
  have heq : dartsSecond G S = (dartsFirst G S).image SimpleGraph.Dart.symm := by
    ext d
    constructor
    · intro hd
      have hdf : d.symm ∈ dartsFirst G S := by
        simp only [dartsFirst, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [dartsSecond] using hd
      exact Finset.mem_image.mpr ⟨d.symm, hdf,
        SimpleGraph.Dart.symm_symm d⟩
    · intro hd
      obtain ⟨d', hd', hEq⟩ := Finset.mem_image.mp hd
      subst hEq
      simp only [dartsFirst, Finset.mem_filter, Finset.mem_univ, true_and] at hd'
      simp only [dartsSecond, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa using hd'
  rw [heq, Finset.card_image_of_injective _
    SimpleGraph.Dart.symm_involutive.injective]
  exact card_dartsFirst_eq_sum_degree G S

lemma even_card_dartsInternal (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Even (dartsInternal G S).card := by
  classical
  refine even_card_of_fixedPointFree_involution_finset (dartsInternal G S)
    (fun d _ => d.symm) ?_ ?_ ?_
  · intro d hd
    simp only [dartsInternal, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    exact ⟨hd.2, hd.1⟩
  · intro d hd
    simpa using d.symm_symm
  · intro d hd
    exact d.symm_ne

lemma dartsFirst_eq_union (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (S : Finset V) :
    dartsFirst G S = dartsInternal G S ∪ dartsBoundary G S := by
  classical
  ext d
  by_cases hsnd : d.snd ∈ S <;>
    simp [dartsFirst, dartsInternal, dartsBoundary, hsnd]

lemma disjoint_dartsInternal_boundary (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Disjoint (dartsInternal G S) (dartsBoundary G S) := by
  classical
  rw [Finset.disjoint_left]
  intro d hdI hdB
  simp only [dartsInternal, dartsBoundary, Finset.mem_filter, Finset.mem_univ,
    true_and] at hdI hdB
  exact hdB.2 hdI.2

lemma odd_card_dartsBoundary_of_cubic_odd
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hCubic : ∀ v, G.degree v = 3)
    {S : Finset V} (hOdd : Odd S.card) :
    Odd (dartsBoundary G S).card := by
  classical
  have hOddFirst : Odd (dartsFirst G S).card := by
    rw [card_dartsFirst_eq_sum_degree G S]
    have hOddSum : Odd (∑ v ∈ S, G.degree v) := by
      simp_rw [hCubic]
      simpa [Finset.sum_const, nsmul_eq_mul] using
        (Odd.mul hOdd (show Odd (3 : Nat) by norm_num))
    exact hOddSum
  have hcard : (dartsFirst G S).card =
      (dartsInternal G S).card + (dartsBoundary G S).card := by
    rw [dartsFirst_eq_union G S, Finset.card_union_of_disjoint]
    exact disjoint_dartsInternal_boundary G S
  have hnotEvenFirst : ¬ Even (dartsFirst G S).card :=
    Nat.not_even_iff_odd.mpr hOddFirst
  apply Nat.not_even_iff_odd.mp
  intro hEvenBoundary
  apply hnotEvenFirst
  rw [hcard]
  exact Nat.even_add.mpr ⟨fun _ => hEvenBoundary, fun _ => even_card_dartsInternal G S⟩

lemma bridge_of_boundary_card_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq V] {S : Finset V}
    (hcard : (dartsBoundary G S).card = 1) :
    ∃ e : Sym2 V, e ∈ G.edgeSet ∧ G.IsBridge e := by
  classical
  obtain ⟨d₀, hd₀⟩ := Finset.card_eq_one.mp hcard
  have hd₀S : d₀.fst ∈ S ∧ d₀.snd ∉ S := by
    have hmem : d₀ ∈ dartsBoundary G S := by
      rw [hd₀]
      simp
    simpa only [dartsBoundary, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
  refine ⟨d₀.edge, d₀.edge_mem, ?_⟩
  change G.IsBridge s(d₀.fst, d₀.snd)
  rw [SimpleGraph.isBridge_iff]
  intro hreach
  obtain ⟨p⟩ := hreach
  let pG : G.Walk d₀.fst d₀.snd :=
    p.mapLe (SimpleGraph.deleteEdges_le {s(d₀.fst, d₀.snd)})
  obtain ⟨d, hd, hdS, hdnotS⟩ :=
    pG.exists_boundary_dart (S : Set V) (by simpa using hd₀S.1) (by simpa using hd₀S.2)
  have hdB : d ∈ dartsBoundary G S := by
    simp only [dartsBoundary, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hdS, hdnotS⟩
  have hdd₀ : d = d₀ := by
    rw [hd₀] at hdB
    simpa using hdB
  have hde : d₀.edge ∈ pG.edges := by
    rw [SimpleGraph.Walk.edges_eq_map_darts]
    exact List.mem_map.mpr ⟨d, hd, by rw [hdd₀]⟩
  have hde' : d₀.edge ∈ p.edges := by
    dsimp [pG] at hde
    have hmap := SimpleGraph.Walk.edges_mapLe_eq_edges
      (SimpleGraph.deleteEdges_le {s(d₀.fst, d₀.snd)}) p
    rw [hmap] at hde
    exact hde
  have hnot : d₀.edge ∉ p.edges := by
    intro hpedge
    have hpedge' := p.edges_subset_edgeSet hpedge
    rw [SimpleGraph.edgeSet_deleteEdges] at hpedge'
    exact hpedge'.2 (by
      change s(d₀.fst, d₀.snd) = s(d₀.fst, d₀.snd)
      rfl)
  exact hnot hde'

end BoundaryDarts

section BoundaryFamilies

lemma boundary_pairwise_disjoint_of_vertex_pairwise_disjoint
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    {C : Finset (Finset V)}
    (hC : (C : Set (Finset V)).PairwiseDisjoint (fun S => (S : Set V))) :
    (C : Set (Finset V)).PairwiseDisjoint (fun S => dartsBoundary G S) := by
  intro S hS T hT hST
  change Disjoint (dartsBoundary G S) (dartsBoundary G T)
  rw [Finset.disjoint_left]
  intro d hdS hdT
  have hS' : d.fst ∈ S := by
    have := (show d.fst ∈ S ∧ d.snd ∉ S from by
      simpa only [dartsBoundary, Finset.mem_filter, Finset.mem_univ, true_and] using hdS)
    exact this.1
  have hT' : d.fst ∈ T := by
    have := (show d.fst ∈ T ∧ d.snd ∉ T from by
      simpa only [dartsBoundary, Finset.mem_filter, Finset.mem_univ, true_and] using hdT)
    exact this.1
  exact (Set.disjoint_left.mp (hC hS hT hST)) hS' hT'

lemma boundary_biUnion_subset_dartsSecond
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    {U : Finset V} {C : Finset (Finset V)}
    (hC : ∀ S ∈ C, dartsBoundary G S ⊆ dartsSecond G U) :
    C.biUnion (fun S => dartsBoundary G S) ⊆ dartsSecond G U := by
  rw [Finset.biUnion_subset]
  exact hC

lemma three_mul_card_le_sum_boundary
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    {C : Finset (Finset V)}
    (hCdisj : (C : Set (Finset V)).PairwiseDisjoint (fun S => (S : Set V)))
    (hCbound : ∀ S ∈ C, 3 ≤ (dartsBoundary G S).card) :
    3 * C.card ≤ ∑ S ∈ C, (dartsBoundary G S).card := by
  have hsum : ∑ S ∈ C, 3 ≤ ∑ S ∈ C, (dartsBoundary G S).card := by
    apply Finset.sum_le_sum
    intro S hS
    exact hCbound S hS
  have hleft : (∑ S ∈ C, 3) = 3 * C.card := by
    simp [Finset.sum_const, nsmul_eq_mul]
    omega
  rw [← hleft]
  exact hsum

lemma sum_boundary_le_three_mul_card
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (hCubic : ∀ v, G.degree v = 3)
    {U : Finset V} {C : Finset (Finset V)}
    (hCdisj : (C : Set (Finset V)).PairwiseDisjoint (fun S => (S : Set V)))
    (hCout : ∀ S ∈ C, dartsBoundary G S ⊆ dartsSecond G U) :
    (∑ S ∈ C, (dartsBoundary G S).card) ≤ 3 * U.card := by
  have hpair := boundary_pairwise_disjoint_of_vertex_pairwise_disjoint G hCdisj
  have hcard := Finset.card_biUnion (s := C) hpair
  have hsub := boundary_biUnion_subset_dartsSecond G hCout
  have hupper : (C.biUnion (fun S => dartsBoundary G S)).card ≤
      (dartsSecond G U).card := Finset.card_le_card hsub
  have hsecond := card_dartsSecond_eq_sum_degree G U
  rw [hcard] at hupper
  rw [hsecond] at hupper
  have hsum : (∑ v ∈ U, G.degree v) = 3 * U.card := by
    simp_rw [hCubic]
    simp [Finset.sum_const, nsmul_eq_mul]
    omega
  rw [hsum] at hupper
  exact hupper

lemma card_family_le_of_three_boundary
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (hCubic : ∀ v, G.degree v = 3)
    {U : Finset V} {C : Finset (Finset V)}
    (hCdisj : (C : Set (Finset V)).PairwiseDisjoint (fun S => (S : Set V)))
    (hCbound : ∀ S ∈ C, 3 ≤ (dartsBoundary G S).card)
    (hCout : ∀ S ∈ C, dartsBoundary G S ⊆ dartsSecond G U) :
    C.card ≤ U.card := by
  have hlower := three_mul_card_le_sum_boundary G hCdisj hCbound
  have hupper := sum_boundary_le_three_mul_card G hCubic hCdisj hCout
  omega

lemma boundary_pairwise_disjoint_indexed
    {ι : Type u} (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    {I : Finset ι} {S : ι → Finset V}
    (hS : (I : Set ι).PairwiseDisjoint (fun i => (S i : Set V))) :
    (I : Set ι).PairwiseDisjoint (fun i => dartsBoundary G (S i)) := by
  intro i hi j hj hij
  change Disjoint (dartsBoundary G (S i)) (dartsBoundary G (S j))
  rw [Finset.disjoint_left]
  intro d hdi hdj
  have hdi' : d.fst ∈ S i := by
    have h := (show d.fst ∈ S i ∧ d.snd ∉ S i from by
      simpa only [dartsBoundary, Finset.mem_filter, Finset.mem_univ, true_and] using hdi)
    exact h.1
  have hdj' : d.fst ∈ S j := by
    have h := (show d.fst ∈ S j ∧ d.snd ∉ S j from by
      simpa only [dartsBoundary, Finset.mem_filter, Finset.mem_univ, true_and] using hdj)
    exact h.1
  exact (Set.disjoint_left.mp (hS hi hj hij)) hdi' hdj'

lemma three_mul_card_le_sum_boundary_indexed
    {ι : Type u} (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    {I : Finset ι} {S : ι → Finset V}
    (hbound : ∀ i ∈ I, 3 ≤ (dartsBoundary G (S i)).card) :
    3 * I.card ≤ ∑ i ∈ I, (dartsBoundary G (S i)).card := by
  have hsum : ∑ i ∈ I, 3 ≤ ∑ i ∈ I, (dartsBoundary G (S i)).card := by
    apply Finset.sum_le_sum
    intro i hi
    exact hbound i hi
  have hleft : (∑ i ∈ I, 3) = 3 * I.card := by
    simp [Finset.sum_const]
    omega
  rw [← hleft]
  exact hsum

lemma sum_boundary_le_three_mul_card_indexed
    {ι : Type u} (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (hCubic : ∀ v, G.degree v = 3)
    {U : Finset V} {I : Finset ι} {S : ι → Finset V}
    (hSdisj : (I : Set ι).PairwiseDisjoint (fun i => (S i : Set V)))
    (hout : ∀ i ∈ I, dartsBoundary G (S i) ⊆ dartsSecond G U) :
    (∑ i ∈ I, (dartsBoundary G (S i)).card) ≤ 3 * U.card := by
  have hpair := boundary_pairwise_disjoint_indexed G hSdisj
  have hcard := Finset.card_biUnion (s := I) hpair
  have hsub : I.biUnion (fun i => dartsBoundary G (S i)) ⊆ dartsSecond G U := by
    rw [Finset.biUnion_subset]
    exact hout
  have hupper : (I.biUnion (fun i => dartsBoundary G (S i))).card ≤
      (dartsSecond G U).card := Finset.card_le_card hsub
  rw [hcard] at hupper
  rw [card_dartsSecond_eq_sum_degree G U] at hupper
  have hsum : (∑ v ∈ U, G.degree v) = 3 * U.card := by
    simp_rw [hCubic]
    simp [Finset.sum_const]
    omega
  rw [hsum] at hupper
  exact hupper

lemma card_index_le_of_three_boundary
    {ι : Type u} (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (hCubic : ∀ v, G.degree v = 3)
    {U : Finset V} {I : Finset ι} {S : ι → Finset V}
    (hSdisj : (I : Set ι).PairwiseDisjoint (fun i => (S i : Set V)))
    (hbound : ∀ i ∈ I, 3 ≤ (dartsBoundary G (S i)).card)
    (hout : ∀ i ∈ I, dartsBoundary G (S i) ⊆ dartsSecond G U) :
    I.card ≤ U.card := by
  have hlower := three_mul_card_le_sum_boundary_indexed G hbound
  have hupper := sum_boundary_le_three_mul_card_indexed G hCubic hSdisj hout
  omega

end BoundaryFamilies

section ComponentFamilies

variable {W : Type u} [Fintype W]

/-- The finite image in the original vertex type of a connected-component
support in an auxiliary graph on `W`. -/
noncomputable def componentImageVerts [DecidableEq V]
    (f : W ↪ V) (H : SimpleGraph W) (c : H.ConnectedComponent) : Finset V :=
  c.supp.toFinite.toFinset.image f

lemma card_componentImageVerts [DecidableEq V]
    (f : W ↪ V) (H : SimpleGraph W) (c : H.ConnectedComponent) :
    (componentImageVerts f H c).card = c.supp.ncard := by
  classical
  rw [componentImageVerts, Finset.card_image_of_injective _ f.injective]
  exact (Set.ncard_eq_toFinset_card c.supp (Set.toFinite _)).symm

lemma pairwise_disjoint_componentImageVerts [DecidableEq V]
    (f : W ↪ V) (H : SimpleGraph W)
    {I : Finset H.ConnectedComponent}
    (hI : (I : Set H.ConnectedComponent).PairwiseDisjoint
      (fun c => (c.supp : Set W))) :
    (I : Set H.ConnectedComponent).PairwiseDisjoint
      (fun c => componentImageVerts f H c) := by
  intro c hc d hd hcd
  change Disjoint (componentImageVerts f H c) (componentImageVerts f H d)
  rw [Finset.disjoint_left]
  intro v hvc hvd
  have hvc' : v ∈ c.supp.toFinite.toFinset.image f := by
    simpa only [componentImageVerts] using hvc
  have hvd' : v ∈ d.supp.toFinite.toFinset.image f := by
    simpa only [componentImageVerts] using hvd
  obtain ⟨x, hxc, hxv⟩ := Finset.mem_image.mp hvc'
  obtain ⟨y, hyd, hyv⟩ := Finset.mem_image.mp hvd'
  have hxy : x = y := f.injective (hxv.trans hyv.symm)
  have hxc' : x ∈ c.supp := c.supp.toFinite.mem_toFinset.mp hxc
  have hyd' : y ∈ d.supp := d.supp.toFinite.mem_toFinset.mp hyd
  exact (Set.disjoint_left.mp (hI hc hd hcd)) hxc' (hxy ▸ hyd')

end ComponentFamilies

section PetersenCounting

/-- No one-edge cut, stated in the form used by the counting proof. -/
def BridgeFree (G : SimpleGraph V) : Prop :=
  ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e

lemma three_le_boundary_of_bridgeFree_cubic_odd
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (hCubic : ∀ v, G.degree v = 3)
    (hFree : BridgeFree G)
    {S : Finset V} (hOdd : Odd S.card) :
    3 ≤ (dartsBoundary G S).card := by
  have hOddBoundary := odd_card_dartsBoundary_of_cubic_odd G hCubic hOdd
  have hne : (dartsBoundary G S).card ≠ 1 := by
    intro hone
    obtain ⟨e, he, hbridge⟩ := bridge_of_boundary_card_one G hone
    exact hFree he hbridge
  obtain ⟨k, hk⟩ := hOddBoundary
  omega

/-- A finite family of disjoint odd vertex sets, each with at least three
boundary darts and with all boundary darts ending in `U`, has no more members
than `U`.  The preceding component lemmas make this applicable to the odd
components in a Tutte test. -/
lemma odd_family_card_le_of_bridgeFree_cubic
    {ι : Type u} (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (hCubic : ∀ v, G.degree v = 3)
    (hFree : BridgeFree G)
    {U : Finset V} {I : Finset ι} {S : ι → Finset V}
    (hSdisj : (I : Set ι).PairwiseDisjoint (fun i => (S i : Set V)))
    (hout : ∀ i ∈ I, dartsBoundary G (S i) ⊆ dartsSecond G U)
    (hodd : ∀ i ∈ I, Odd (S i).card) :
    I.card ≤ U.card := by
  apply card_index_le_of_three_boundary G hCubic hSdisj
  · intro i hi
    exact three_le_boundary_of_bridgeFree_cubic_odd G hCubic hFree (hodd i hi)
  · exact hout

end PetersenCounting

section TutteNoViolator

/-- The standard Petersen counting theorem is expressed here with the
finite-degree convention used by Mathlib.  The proof reduces a hypothetical
Tutte violator to the boundary-family estimate above; all component supports
are mapped back from the deleted-vertex graph to `V`. -/
theorem no_tutte_violator_of_bridgeFree_cubic
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (hCubic : ∀ v, G.degree v = 3)
    (hFree : BridgeFree G)
    (U : Set V) :
    ¬ G.IsTutteViolator U := by
  classical
  intro hviol
  let W := ((⊤ : G.Subgraph).deleteVerts U).verts
  let H : SimpleGraph W := ((⊤ : G.Subgraph).deleteVerts U).coe
  let f : W ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let I : Finset H.ConnectedComponent := H.oddComponents.toFinite.toFinset
  let S : H.ConnectedComponent → Finset V :=
    fun c => componentImageVerts f H c
  have hIcard : I.card = H.oddComponents.ncard := by
    dsimp [I]
    exact (Set.ncard_eq_toFinset_card H.oddComponents (Set.toFinite _)).symm
  have hIcomp : (I : Set H.ConnectedComponent).PairwiseDisjoint
      (fun c => (c.supp : Set W)) := by
    intro c hc d hd hcd
    exact SimpleGraph.pairwise_disjoint_supp_connectedComponent H hcd
  have hIodd : ∀ c ∈ I, Odd (S c).card := by
    intro c hc
    have hc' : c ∈ H.oddComponents := by
      exact H.oddComponents.toFinite.mem_toFinset.mp (by simpa [I] using hc)
    rw [card_componentImageVerts f H c]
    exact hc'
  have hSdisj : (I : Set H.ConnectedComponent).PairwiseDisjoint
      (fun c => (S c : Set V)) := by
    simpa [S] using pairwise_disjoint_componentImageVerts f H hIcomp
  have hbound : ∀ c ∈ I, 3 ≤ (dartsBoundary G (S c)).card := by
    intro c hc
    exact three_le_boundary_of_bridgeFree_cubic_odd G hCubic hFree (hIodd c hc)
  have hout : ∀ c ∈ I,
      dartsBoundary G (S c) ⊆ dartsSecond G U.toFinite.toFinset := by
    intro c hc d hd
    have hdparts : d.fst ∈ S c ∧ d.snd ∉ S c := by
      simpa only [dartsBoundary, Finset.mem_filter, Finset.mem_univ, true_and] using hd
    simp only [dartsSecond, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hnotUfin
    have hnotU : d.snd ∉ U := by
      intro hU
      exact hnotUfin (U.toFinite.mem_toFinset.mpr hU)
    have hdfin : d.fst ∈ c.supp.toFinite.toFinset.image f := by
      simpa only [S, componentImageVerts] using hdparts.1
    obtain ⟨x, hx, hxf⟩ := Finset.mem_image.mp hdfin
    have hxcomp : x ∈ c.supp := c.supp.toFinite.mem_toFinset.mp hx
    have hyW : d.snd ∈ W := by
      change d.snd ∈ ((⊤ : G.Subgraph).deleteVerts U).verts
      rw [SimpleGraph.Subgraph.deleteVerts_verts]
      simp [hnotU]
    let y : W := ⟨d.snd, hyW⟩
    have hxnotU : f x ∉ U := by
      have hxW' := x.property
      change (x : V) ∈ ((⊤ : G.Subgraph).deleteVerts U).verts at hxW'
      rw [SimpleGraph.Subgraph.deleteVerts_verts] at hxW'
      simpa [f] using hxW'.2
    have hGadj : G.Adj (f x) d.snd := by
      rw [hxf]
      exact d.adj
    have hadjH : H.Adj x y := by
      simpa [H, SimpleGraph.Subgraph.coe_adj, SimpleGraph.Subgraph.deleteVerts_adj,
        f, y, hnotU, hxnotU, hGadj] using
        (show f x ∉ U ∧ G.Adj (f x) d.snd from ⟨hxnotU, hGadj⟩)
    have hycomp : y ∈ c.supp := c.mem_supp_of_adj_mem_supp hxcomp hadjH
    have hyfin : y ∈ c.supp.toFinite.toFinset := c.supp.toFinite.mem_toFinset.mpr hycomp
    have hyn : f y ∈ componentImageVerts f H c := by
      rw [componentImageVerts]
      exact Finset.mem_image.mpr ⟨y, hyfin, rfl⟩
    have hds : d.snd ∈ S c := by
      change f y ∈ S c
      simpa [S] using hyn
    exact hdparts.2 hds
  have hle : I.card ≤ U.toFinite.toFinset.card :=
    odd_family_card_le_of_bridgeFree_cubic G hCubic hFree hSdisj hout hIodd
  have hUcard : U.toFinite.toFinset.card = U.ncard :=
    (Set.ncard_eq_toFinset_card U (Set.toFinite _)).symm
  have hviol' : U.ncard < I.card := by
    rw [hIcard]
    simpa only [SimpleGraph.IsTutteViolator, H] using hviol
  rw [hUcard] at hle
  omega

end TutteNoViolator

section ProjectMatching


end ProjectMatching
end
end R03SP03PetersenMatching

open CubicP3Partition
open scoped BigOperators
universe u
variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {W : Type u} [Fintype W]
theorem solution
    {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsPerfectMatching) :
    CubicP3Partition.PerfectMatching G M.spanningCoe := by
  refine ⟨M.spanningCoe_le, ?_⟩
  intro v
  letI : Fintype {w : V // M.Adj v w} := Fintype.ofFinite _
  change Nat.card {w : V // M.Adj v w} = 1
  rw [Nat.card_eq_fintype_card]
  apply Fintype.card_eq_one_iff.mpr
  obtain ⟨w, hw, huw⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM) v
  refine ⟨⟨w, hw⟩, ?_⟩
  intro z
  exact Subtype.ext (huw z.val z.property)

