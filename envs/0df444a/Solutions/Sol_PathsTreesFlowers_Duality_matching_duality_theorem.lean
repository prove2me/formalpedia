-- Prove2me | solution 1 for PathsTreesFlowers.Duality.matching_duality_theorem
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-11T05:22:15.050127+00:00
-- url     : https://prove2.me/submissions/016c722d-d2e1-4090-ac04-2423159847b9

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic
import Definitions.Def_PathsTreesFlowers_Duality_OddSetCover

-- BEGIN COMPLETE MODULE NativeMatching
section

namespace PathsTreesFlowers.Duality.Proof
open EdmondsMatching65.Polyhedron
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def underlying (G : EdmondsMatching65.Polyhedron.Graph V E) : SimpleGraph V where
  Adj u v := ∃ e, G.ends e = s(u,v)
  symm := ⟨by rintro u v ⟨e, he⟩; exact ⟨e, he.trans Sym2.eq_swap⟩⟩
  loopless := ⟨by rintro v ⟨e, he⟩; apply G.loopless e; rw [he]; simp⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma matching_endpoints_disjoint (G : EdmondsMatching65.Polyhedron.Graph V E) {M : Finset E} (hM : IsMatching G M) :
    (M : Set E).PairwiseDisjoint (fun e => (G.ends e).toFinset) := by
  intro e he f hf hne
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact hM e he f hf hne v (Sym2.mem_toFinset.mp hv) (Sym2.mem_toFinset.mp hw)

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma matching_card_bound (G : EdmondsMatching65.Polyhedron.Graph V E) {M : Finset E} (hM : IsMatching G M)
    (U : Finset V) (hU : ∀ e ∈ M, G.ends e ∈ U.sym2) : 2 * M.card ≤ U.card := by
  have hs : M.biUnion (fun e => (G.ends e).toFinset) ⊆ U := by
    intro v hv
    obtain ⟨e, he, hv⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_sym2_iff.mp (hU e he) v (Sym2.mem_toFinset.mp hv)
  have hc := Finset.card_le_card hs
  rw [Finset.card_biUnion (matching_endpoints_disjoint G hM)] at hc
  simpa [Sym2.card_toFinset_of_not_isDiag, G.loopless, mul_comm] using hc

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma matching_restrict (G : EdmondsMatching65.Polyhedron.Graph V E) {M N : Finset E} (hM : IsMatching G M)
    (hN : N ⊆ M) : IsMatching G N := by
  exact fun e he f hf hne v hv => hM e (hN he) f (hN hf) hne v hv

omit [Fintype V] [Fintype E] in
lemma matching_singleton_count (G : EdmondsMatching65.Polyhedron.Graph V E) {M : Finset E} (hM : IsMatching G M)
    (v : V) : (M.filter (fun e => v ∈ G.ends e)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨he, hev⟩ := Finset.mem_filter.mp he
  obtain ⟨hf, hfv⟩ := Finset.mem_filter.mp hf
  by_contra hne
  exact hM e he f hf hne v hev hfv

omit [Fintype V] [Fintype E] in
lemma matching_cover_count (G : EdmondsMatching65.Polyhedron.Graph V E) {M : Finset E} (hM : IsMatching G M)
    {U : Finset V} (hU : IsOddSet U) :
    (M.filter (Covers G U)).card ≤ capacity U := by
  classical
  by_cases h1 : U.card = 1
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h1
    have he : Covers G {v} = (fun e => v ∈ G.ends e) := by funext e; simp [Covers]
    have heF : M.filter (Covers G {v}) = M.filter (fun e => v ∈ G.ends e) := by
      apply Finset.filter_congr; intro e _; simp only [he]
    rw [heF]
    simpa [capacity] using matching_singleton_count G hM v
  · have hb := matching_card_bound G (matching_restrict G hM (Finset.filter_subset (Covers G U) M)) U
      (fun e he => by simpa [Covers, h1] using (Finset.mem_filter.mp he).2)
    obtain ⟨k, hk⟩ := hU
    simp only [capacity, h1, if_false]
    omega

omit [Fintype V] [Fintype E] in
lemma weak_duality (G : EdmondsMatching65.Polyhedron.Graph V E) {M : Finset E} (hM : IsMatching G M)
    {S : Finset (Finset V)} (hS : IsOddSetCover G S) : M.card ≤ capacitySum S := by
  classical
  have hc : M ⊆ S.biUnion (fun U => M.filter (Covers G U)) := by
    intro e he
    obtain ⟨U, hU, hc⟩ := hS.2 e
    exact Finset.mem_biUnion.mpr ⟨U, hU, Finset.mem_filter.mpr ⟨he,hc⟩⟩
  exact (Finset.card_le_card hc).trans ((Finset.card_biUnion_le).trans
    (Finset.sum_le_sum fun U hU => matching_cover_count G hM (hS.1 U hU)))

end PathsTreesFlowers.Duality.Proof
end
-- END COMPLETE MODULE NativeMatching

-- BEGIN COMPLETE MODULE MatchingTransfer
section

namespace PathsTreesFlowers.Duality.Proof
open EdmondsMatching65.Polyhedron
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma underlying_edge (G : EdmondsMatching65.Polyhedron.Graph V E) {s : Sym2 V}
    (hs : s ∈ (underlying G).edgeSet) : ∃ e, G.ends e = s := by
  induction s using Sym2.inductionOn with
  | _ u v => exact hs

omit [Fintype V] [DecidableEq V] in
lemma matching_edges_disjoint {G : SimpleGraph V} {M : G.Subgraph} (hM : M.IsMatching)
    {e f : Sym2 V} (he : e ∈ M.edgeSet) (hf : f ∈ M.edgeSet) (hne : e ≠ f)
    {v : V} (hev : v ∈ e) : v ∉ f := by
  intro hfv
  obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp hev
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hfv
  have he' : M.Adj v u := he
  have hf' : M.Adj v w := hf
  exact hne (congrArg (fun x => s(v,x)) (hM.eq_of_adj_left he' hf'))

omit [DecidableEq V] [Fintype E] in
lemma native_matching_of_simple (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : (underlying G).Subgraph) (hM : M.IsMatching) :
    ∃ N : Finset E, IsMatching G N ∧ N.card = M.edgeSet.ncard := by
  classical
  let chooseEdge : M.edgeSet → E := fun e => (underlying_edge G (M.edgeSet_subset e.property)).choose
  have hchoose : ∀ e : M.edgeSet, G.ends (chooseEdge e) = e.val :=
    fun e => (underlying_edge G (M.edgeSet_subset e.property)).choose_spec
  have hinj : Function.Injective chooseEdge := by
    intro e f hef
    apply Subtype.ext
    rw [← hchoose e, ← hchoose f, hef]
  let N := Finset.univ.image chooseEdge
  refine ⟨N, ?_, ?_⟩
  · intro e he f hf hne v hev hfv
    obtain ⟨e', -, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨f', -, rfl⟩ := Finset.mem_image.mp hf
    rw [hchoose] at hev hfv
    exact matching_edges_disjoint hM e'.property f'.property
      (fun h => hne (congrArg chooseEdge (Subtype.ext h))) hev hfv
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    exact Nat.card_eq_fintype_card.symm.trans (Nat.card_coe_set_eq _)

end PathsTreesFlowers.Duality.Proof
end
-- END COMPLETE MODULE MatchingTransfer

-- BEGIN COMPLETE MODULE Deficiency
section

namespace PathsTreesFlowers.Duality.Proof
variable {V : Type} [Fintype V]

abbrev residual (G : SimpleGraph V) (S : Finset V) :=
  ((⊤ : G.Subgraph).deleteVerts (S : Set V)).coe

noncomputable def oddCount (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (residual G S).oddComponents.ncard

lemma residual_card (G : SimpleGraph V) (S : Finset V) :
    Nat.card ((⊤ : G.Subgraph).deleteVerts (S : Set V)).verts + S.card = Fintype.card V := by
  rw [SimpleGraph.Subgraph.deleteVerts_verts, SimpleGraph.Subgraph.verts_top,
    ← Set.compl_eq_univ_sdiff, Nat.card_coe_set_eq]
  simpa only [Set.ncard_coe_finset, Nat.card_eq_fintype_card] using
    Set.ncard_compl_add_ncard (S : Set V)

lemma oddCount_parity (G : SimpleGraph V) (S : Finset V) :
    (oddCount G S + S.card) % 2 = Fintype.card V % 2 := by
  have h := SimpleGraph.odd_ncard_oddComponents (residual G S)
  have hc := residual_card G S
  change Odd (oddCount G S) ↔ Odd _ at h
  simp only [Nat.odd_iff] at h
  omega

lemma exists_max_deficiency (G : SimpleGraph V) :
    ∃ S : Finset V, ∀ T : Finset V, oddCount G T + S.card ≤ oddCount G S + T.card := by
  classical
  obtain ⟨S, -, hS⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset V))
    (fun T => (oddCount G T : ℤ) - T.card) (Finset.univ_nonempty)
  refine ⟨S, fun T => ?_⟩
  have h := hS T (Finset.mem_univ T)
  omega

lemma deficiency_data (G : SimpleGraph V) {S : Finset V}
    (hS : ∀ T, oddCount G T + S.card ≤ oddCount G S + T.card) :
    ∃ d : ℕ, oddCount G S = S.card + d ∧ Even (Nat.card V + d) ∧
      ∀ U : Set V, (((⊤ : G.Subgraph).deleteVerts U).coe).oddComponents.ncard ≤ U.ncard + d := by
  classical
  have hn := hS ∅
  simp only [Finset.card_empty, Nat.add_zero] at hn
  let d := oddCount G S - S.card
  have he : oddCount G S = S.card + d := by dsimp [d]; omega
  refine ⟨d, he, ?_, ?_⟩
  · have hp := oddCount_parity G S
    rw [Nat.even_iff]
    rw [Nat.card_eq_fintype_card]
    omega
  · intro U
    have h := hS U.toFinset
    have heU : (U.toFinset : Set V) = U := Set.coe_toFinset U
    have hb : oddCount G U.toFinset ≤ U.toFinset.card + d := by omega
    change (((⊤ : G.Subgraph).deleteVerts (U.toFinset : Set V)).coe).oddComponents.ncard ≤ _ at hb
    rw [heU] at hb
    simpa only [← Set.ncard_eq_toFinset_card'] using hb

end PathsTreesFlowers.Duality.Proof
end
-- END COMPLETE MODULE Deficiency

-- BEGIN COMPLETE MODULE ComponentCount
section

namespace PathsTreesFlowers.Duality.Proof

lemma sum_component_cards {W : Type} [Fintype W] (G : SimpleGraph W) [Fintype G.ConnectedComponent] :
    ∑ c : G.ConnectedComponent, c.supp.ncard = Fintype.card W := by
  classical
  rw [← (set_fintype_card_eq_univ_iff _).mpr G.iUnion_connectedComponentSupp,
    ← Set.toFinset_card, Set.toFinset_iUnion SimpleGraph.ConnectedComponent.supp]
  rw [Finset.card_biUnion
    (fun x _ y _ hxy => Set.disjoint_toFinset.mpr
      (SimpleGraph.pairwise_disjoint_supp_connectedComponent _ hxy))]
  simp only [← Set.ncard_eq_toFinset_card']

lemma component_half_sum {W : Type} [Fintype W] (G : SimpleGraph W) [Fintype G.ConnectedComponent] :
    2 * (∑ c : G.ConnectedComponent, c.supp.ncard / 2) + G.oddComponents.ncard =
      Fintype.card W := by
  classical
  have hc : G.oddComponents.ncard = ∑ c : G.ConnectedComponent,
      if Odd c.supp.ncard then 1 else 0 := by
    rw [Set.ncard_eq_toFinset_card']
    simp only [SimpleGraph.oddComponents, Set.toFinset_ofPred, Finset.sum_boole]
    rfl
  rw [hc, Finset.mul_sum]
  change (∑ c : G.ConnectedComponent, 2 * (c.supp.ncard / 2)) +
    (∑ c : G.ConnectedComponent, if Odd c.supp.ncard then 1 else 0) = _
  rw [← Finset.sum_add_distrib]
  calc
    ∑ c : G.ConnectedComponent, (2 * (c.supp.ncard / 2) + if Odd c.supp.ncard then 1 else 0) =
      ∑ c : G.ConnectedComponent, c.supp.ncard := by
        apply Finset.sum_congr rfl
        intro c _
        split_ifs with h <;> simp only [Nat.odd_iff] at h <;> omega
    _ = Fintype.card W := sum_component_cards G

variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable instance residual_fintype (G : SimpleGraph V) (S : Finset V) :
    Fintype ((⊤ : G.Subgraph).deleteVerts (S : Set V)).verts := Fintype.ofFinite _

noncomputable instance residual_components_fintype (G : SimpleGraph V) (S : Finset V) :
    Fintype (residual G S).ConnectedComponent := Fintype.ofFinite _

noncomputable def componentVertices (G : SimpleGraph V) (S : Finset V)
    (c : (residual G S).ConnectedComponent) : Finset V := by
  classical
  exact c.supp.toFinset.image Subtype.val

lemma componentVertices_card (G : SimpleGraph V) (S : Finset V)
    (c : (residual G S).ConnectedComponent) :
    (componentVertices G S c).card = c.supp.ncard := by
  classical
  unfold componentVertices
  rw [Finset.card_image_of_injective _ Subtype.val_injective]
  exact (Set.ncard_eq_toFinset_card' _).symm

lemma component_cover_budget (G : SimpleGraph V) (S : Finset V) :
    2 * (S.card + ∑ c : (residual G S).ConnectedComponent,
      (componentVertices G S c).card / 2) + oddCount G S = Fintype.card V + S.card := by
  have h := component_half_sum (residual G S)
  have hr := residual_card G S
  simp only [componentVertices_card] at *
  change 2 * _ + oddCount G S = _ at h
  rw [← Nat.card_eq_fintype_card] at h
  omega

end PathsTreesFlowers.Duality.Proof
end
-- END COMPLETE MODULE ComponentCount

-- BEGIN COMPLETE MODULE LocalOddCover
section

namespace PathsTreesFlowers.Duality.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma endpoint_finset_card (G : EdmondsMatching65.Polyhedron.Graph V E) (e : E) :
    (G.ends e).toFinset.card = 2 := Sym2.card_toFinset_of_not_isDiag _ (G.loopless e)

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma no_edge_small (G : EdmondsMatching65.Polyhedron.Graph V E) {U : Finset V}
    (hU : U.card ≤ 1) (e : E) : G.ends e ∉ U.sym2 := by
  intro he
  have hsub : (G.ends e).toFinset ⊆ U := by
    intro v hv; exact Finset.mem_sym2_iff.mp he v (Sym2.mem_toFinset.mp hv)
  have := Finset.card_le_card hsub
  rw [endpoint_finset_card] at this
  omega

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma covers_singleton (G : EdmondsMatching65.Polyhedron.Graph V E) {e : E} {v : V}
    (hv : v ∈ G.ends e) : Covers G {v} e := by simp [Covers, hv]

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma endpoints_erase (G : EdmondsMatching65.Polyhedron.Graph V E) {U : Finset V}
    {v : V} {e : E} (he : G.ends e ∈ U.sym2) (hv : v ∉ G.ends e) :
    G.ends e ∈ (U.erase v).sym2 := by
  apply Finset.mem_sym2_iff.mpr
  intro w hw
  exact Finset.mem_erase.mpr ⟨fun h => hv (h ▸ hw), Finset.mem_sym2_iff.mp he w hw⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma local_odd_cover (G : EdmondsMatching65.Polyhedron.Graph V E) (U : Finset V) :
    ∃ S : Finset (Finset V),
      (∀ A ∈ S, IsOddSet A) ∧
      (∀ e, G.ends e ∈ U.sym2 → ∃ A ∈ S, Covers G A e) ∧
      capacitySum S ≤ U.card / 2 := by
  classical
  by_cases hsmall : U.card ≤ 1
  · refine ⟨∅, by simp, ?_, by simp [capacitySum]⟩
    intro e he
    exact (no_edge_small G hsmall e he).elim
  by_cases hodd : Odd U.card
  · refine ⟨{U}, ?_, ?_, ?_⟩
    · simpa [IsOddSet] using hodd
    · intro e he
      refine ⟨U, by simp, ?_⟩
      simpa [Covers, show U.card ≠ 1 by omega] using he
    · simp only [capacitySum, Finset.sum_singleton, capacity,
        if_neg (show U.card ≠ 1 by omega)]
      omega
  have hpos : U.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hpos
  have herase := Finset.card_erase_of_mem hv
  by_cases htwo : U.card = 2
  · refine ⟨{{v}}, ?_, ?_, ?_⟩
    · simp [IsOddSet]
    · intro e he
      refine ⟨{v}, by simp, covers_singleton G ?_⟩
      by_contra hnot
      exact no_edge_small G (by omega) e (endpoints_erase G he hnot)
    · simp [capacitySum, capacity, htwo]
  · have heodd : Odd (U.erase v).card := by
      simp only [Nat.odd_iff] at hodd ⊢
      omega
    have hene : (U.erase v).card ≠ 1 := by omega
    have hdiff : U.erase v ≠ {v} := by
      intro h
      have : v ∈ U.erase v := h ▸ Finset.mem_singleton_self v
      simp at this
    refine ⟨{U.erase v, {v}}, ?_, ?_, ?_⟩
    · intro A hA
      simp only [Finset.mem_insert, Finset.mem_singleton] at hA
      rcases hA with rfl | rfl
      · exact heodd
      · simp [IsOddSet]
    · intro e he
      by_cases hve : v ∈ G.ends e
      · exact ⟨{v}, by simp, covers_singleton G hve⟩
      · refine ⟨U.erase v, by simp, ?_⟩
        simpa [Covers, hene] using endpoints_erase G he hve
    · have hn : U.erase v ∉ ({ {v} } : Finset (Finset V)) := by simpa using hdiff
      rw [capacitySum, Finset.sum_insert hn, Finset.sum_singleton]
      simp only [capacity, if_neg hene, Finset.card_singleton, ↓reduceIte]
      omega

end PathsTreesFlowers.Duality.Proof
end
-- END COMPLETE MODULE LocalOddCover

-- BEGIN COMPLETE MODULE ComponentCover
section

namespace PathsTreesFlowers.Duality.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in
lemma edge_in_component (G : EdmondsMatching65.Polyhedron.Graph V E) (S : Finset V)
    (e : E) (hS : ∀ v ∈ G.ends e, v ∉ S) :
    ∃ c : (residual (underlying G) S).ConnectedComponent,
      G.ends e ∈ (componentVertices (underlying G) S c).sym2 := by
  classical
  obtain ⟨⟨u,v⟩, he⟩ := Sym2.mk_surjective (G.ends e)
  change s(u,v) = G.ends e at he
  have hu : u ∉ S := hS u (he ▸ Sym2.mem_mk_left u v)
  have hv : v ∉ S := hS v (he ▸ Sym2.mem_mk_right u v)
  let u' : ((⊤ : (underlying G).Subgraph).deleteVerts (S:Set V)).verts :=
    ⟨u, by simp [hu]⟩
  let v' : ((⊤ : (underlying G).Subgraph).deleteVerts (S:Set V)).verts :=
    ⟨v, by simp [hv]⟩
  have hadj : (residual (underlying G) S).Adj u' v' := by
    change ((⊤ : (underlying G).Subgraph).deleteVerts (S:Set V)).Adj u v
    simp only [SimpleGraph.Subgraph.deleteVerts_adj, SimpleGraph.Subgraph.verts_top,
      Set.mem_univ, Finset.mem_coe, true_and, SimpleGraph.Subgraph.top_adj]
    exact ⟨hu,hv,e,he.symm⟩
  let c := (residual (underlying G) S).connectedComponentMk u'
  have huC : u' ∈ c.supp := rfl
  have hvC : v' ∈ c.supp := c.mem_supp_of_adj_mem_supp huC hadj
  refine ⟨c, ?_⟩
  rw [← he, Finset.mk_mem_sym2_iff]
  constructor
  · exact Finset.mem_image.mpr ⟨u', Set.mem_toFinset.mpr huC, rfl⟩
  · exact Finset.mem_image.mpr ⟨v', Set.mem_toFinset.mpr hvC, rfl⟩

omit [Fintype V] in
lemma capacitySum_union_le (S T : Finset (Finset V)) :
    capacitySum (S ∪ T) ≤ capacitySum S + capacitySum T := by
  have h := Finset.sum_union_inter (s₁:=S) (s₂:=T) (f:=capacity)
  unfold capacitySum
  omega

omit [Fintype V] in
lemma capacitySum_biUnion_le {ι : Type} (s : Finset ι) (F : ι → Finset (Finset V)) :
    capacitySum (s.biUnion F) ≤ ∑ i ∈ s, capacitySum (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [capacitySum]
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact (capacitySum_union_le _ _).trans (Nat.add_le_add_left ih _)

omit [Fintype E] [DecidableEq E] in
lemma deletion_cover (G : EdmondsMatching65.Polyhedron.Graph V E) (S : Finset V) :
    ∃ C : Finset (Finset V), IsOddSetCover G C ∧
      capacitySum C ≤ S.card + ∑ c : (residual (underlying G) S).ConnectedComponent,
        (componentVertices (underlying G) S c).card / 2 := by
  classical
  let R := residual (underlying G) S
  let cv := componentVertices (underlying G) S
  choose F hodd hcov hcap using fun c : R.ConnectedComponent => local_odd_cover G (cv c)
  let singles := S.image (fun v => ({v} : Finset V))
  let C := singles ∪ Finset.univ.biUnion F
  have hsingle : capacitySum singles = S.card := by
    unfold capacitySum singles
    rw [Finset.sum_image]
    · simp [capacity]
    · intro a _ b _ hab
      simpa using hab
  refine ⟨C, ⟨?_, ?_⟩, ?_⟩
  · intro U hU
    rcases Finset.mem_union.mp hU with hU | hU
    · obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hU
      simp [IsOddSet]
    · obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp hU
      exact hodd c U hc
  · intro e
    by_cases he : ∃ v ∈ G.ends e, v ∈ S
    · obtain ⟨v,hv,hS⟩ := he
      exact ⟨{v}, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,hS,rfl⟩),
        covers_singleton G hv⟩
    · obtain ⟨c,hc⟩ := edge_in_component G S e (by simpa using he)
      obtain ⟨U,hU,hce⟩ := hcov c e hc
      exact ⟨U,Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c,Finset.mem_univ _,hU⟩),hce⟩
  · calc
      capacitySum C ≤ capacitySum singles + capacitySum (Finset.univ.biUnion F) :=
        capacitySum_union_le _ _
      _ ≤ S.card + ∑ c : R.ConnectedComponent, capacitySum (F c) := by
        rw [hsingle]
        exact Nat.add_le_add_left (capacitySum_biUnion_le _ _) _
      _ ≤ S.card + ∑ c : R.ConnectedComponent, (cv c).card / 2 :=
        Nat.add_le_add_left (Finset.sum_le_sum fun c _ => hcap c) _

end PathsTreesFlowers.Duality.Proof
end
-- END COMPLETE MODULE ComponentCover

-- BEGIN COMPLETE MODULE AugmentGraph
section

namespace PathsTreesFlowers.Duality.Proof
open SimpleGraph Set
variable {V W : Type*}

def augmented (G : SimpleGraph V) (d : ℕ) : SimpleGraph (V ⊕ Fin d) where
  Adj u v := match u,v with
    | .inl x,.inl y => G.Adj x y
    | _,_ => u ≠ v
  symm := ⟨by intro u v; cases u <;> cases v <;> simp_all [G.adj_comm, ne_comm]⟩
  loopless := ⟨by intro u; cases u <;> simp⟩

@[simp] lemma augmented_left (G : SimpleGraph V) (d : ℕ) (x y : V) :
    (augmented G d).Adj (.inl x) (.inl y) ↔ G.Adj x y := Iff.rfl

lemma augmented_universal (G : SimpleGraph V) (d : ℕ) (i : Fin d)
    (u : V ⊕ Fin d) (hne : u ≠ .inr i) : (augmented G d).Adj u (.inr i) := by
  cases u <;> exact hne

lemma iso_odd_count [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : G.oddComponents.ncard = H.oddComponents.ncard := by
  have hc (C : G.ConnectedComponent) : C.supp.ncard = (e.connectedComponentEquiv C).supp.ncard := by
    exact Nat.card_congr (C.isoEquivSupp e)
  let f : G.oddComponents ≃ H.oddComponents := e.connectedComponentEquiv.subtypeEquiv
    (fun C => by change Odd C.supp.ncard ↔ Odd (e.connectedComponentEquiv C).supp.ncard; rw [hc C])
  exact Nat.card_congr f

lemma preconnected_odd_le_one [Finite V] {G : SimpleGraph V} (h : G.Preconnected) :
    G.oddComponents.ncard ≤ 1 := by
  let : Subsingleton G.ConnectedComponent := h.subsingleton_connectedComponent
  exact Set.ncard_le_one_of_subsingleton _

lemma preconnected_odd_zero [Finite V] {G : SimpleGraph V} (h : G.Preconnected)
    (he : Even (Nat.card V)) : G.oddComponents.ncard = 0 := by
  have hle := preconnected_odd_le_one h
  have hnot : ¬ Odd G.oddComponents.ncard := by
    rw [G.odd_ncard_oddComponents]
    exact Nat.not_odd_iff_even.mpr he
  rw [Nat.not_odd_iff] at hnot
  omega

end PathsTreesFlowers.Duality.Proof
end
-- END COMPLETE MODULE AugmentGraph

-- BEGIN COMPLETE MODULE AugmentDelete
section

namespace PathsTreesFlowers.Duality.Proof
open SimpleGraph Set
variable {V : Type*} (G : SimpleGraph V) (d : ℕ)

noncomputable def deletedLeftIso (U : Set (V ⊕ Fin d)) (hU : ∀ i, Sum.inr i ∈ U) :
    ((⊤ : G.Subgraph).deleteVerts (Sum.inl ⁻¹' U)).coe ≃g
      ((⊤ : (augmented G d).Subgraph).deleteVerts U).coe := by
  let f : ((⊤ : G.Subgraph).deleteVerts (Sum.inl ⁻¹' U)).verts →
      ((⊤ : (augmented G d).Subgraph).deleteVerts U).verts :=
    fun x => ⟨Sum.inl x.val, by simpa using x.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      exact Sum.inl.inj (congrArg Subtype.val h)
    · rintro ⟨u,hu⟩
      cases u with
      | inl x => exact ⟨⟨x,by simpa using hu⟩,rfl⟩
      | inr i => exact False.elim ((by simpa using hu : Sum.inr i ∉ U) (hU i))
  refine { Equiv.ofBijective f hf with map_rel_iff' := ?_ }
  intro x y
  simp [f,SimpleGraph.Subgraph.coe_adj]

lemma augmented_delete_preconnected (U : Set (V ⊕ Fin d)) (i : Fin d)
    (hi : Sum.inr i ∉ U) :
    (((⊤ : (augmented G d).Subgraph).deleteVerts U).coe).Preconnected := by
  let z : ((⊤ : (augmented G d).Subgraph).deleteVerts U).verts :=
    ⟨Sum.inr i,by simpa using hi⟩
  have hr (x : ((⊤ : (augmented G d).Subgraph).deleteVerts U).verts) :
      (((⊤ : (augmented G d).Subgraph).deleteVerts U).coe).Reachable x z := by
    by_cases h : x=z
    · subst x; exact SimpleGraph.Reachable.refl z
    · apply SimpleGraph.Adj.reachable
      apply SimpleGraph.Subgraph.Adj.coe
      apply SimpleGraph.Subgraph.deleteVerts_adj.mpr
      refine ⟨Set.mem_univ _,?_,Set.mem_univ _,hi,?_⟩
      · exact x.property.2
      · apply augmented_universal
        intro he
        exact h (Subtype.ext he)
  intro x y
  exact (hr x).trans (hr y).symm

end PathsTreesFlowers.Duality.Proof
end
-- END COMPLETE MODULE AugmentDelete

-- BEGIN COMPLETE MODULE AugmentTutte
section

namespace PathsTreesFlowers.Duality.Proof
open SimpleGraph Set
variable {V : Type*} [Finite V]

lemma deleted_card_all_new (d : ℕ) (U : Set (V ⊕ Fin d)) (hU : ∀ i, Sum.inr i ∈ U) :
    U.ncard = (Sum.inl ⁻¹' U : Set V).ncard+d := by
  have he : U = Sum.inl '' (Sum.inl ⁻¹' U : Set V) ∪ Sum.inr '' (Set.univ : Set (Fin d)) := by
    ext u; cases u <;> simp [hU]
  have hd : Disjoint (Sum.inl '' (Sum.inl ⁻¹' U : Set V))
      (Sum.inr '' (Set.univ : Set (Fin d))) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,_,rfl⟩ ⟨y,_,h⟩
    cases h
  conv_lhs => rw [he, Set.ncard_union_eq hd]
  rw [Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_image_of_injective _ Sum.inr_injective]
  simp

lemma augmented_tutte (G : SimpleGraph V) (d : ℕ) (heven : Even (Nat.card V+d))
    (hbound : ∀ U : Set V, (((⊤ : G.Subgraph).deleteVerts U).coe).oddComponents.ncard ≤ U.ncard+d) :
    ∃ M : (augmented G d).Subgraph, M.IsPerfectMatching := by
  classical
  apply SimpleGraph.tutte.mpr
  intro U
  change ¬ U.ncard < (((⊤ : (augmented G d).Subgraph).deleteVerts U).coe).oddComponents.ncard
  apply not_lt_of_ge
  by_cases hnew : ∀ i, Sum.inr i ∈ U
  · rw [←iso_odd_count (deletedLeftIso G d U hnew),deleted_card_all_new d U hnew]
    exact hbound _
  · push Not at hnew
    obtain ⟨i,hi⟩ := hnew
    have hc := augmented_delete_preconnected G d U i hi
    by_cases hU : U=∅
    · subst U
      have he : Even (Nat.card (((⊤ : (augmented G d).Subgraph).deleteVerts ∅).verts)) := by
        simpa using heven
      rw [preconnected_odd_zero hc he]
      exact Nat.zero_le _
    · exact (preconnected_odd_le_one hc).trans ((Set.ncard_pos (Set.toFinite U)).mpr (Set.nonempty_iff_ne_empty.mpr hU))

end PathsTreesFlowers.Duality.Proof
end
-- END COMPLETE MODULE AugmentTutte

-- BEGIN COMPLETE MODULE MatchingCard
section

namespace PathsTreesFlowers.Duality.Proof
open SimpleGraph Set
variable {V : Type*} [Finite V] {G : SimpleGraph V}

lemma matching_vertex_card {M : G.Subgraph} (hM : M.IsMatching) :
    M.verts.ncard = 2*M.edgeSet.ncard := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have h := M.coe.sum_degrees_eq_twice_card_edges
  have hc : M.coe.edgeFinset.card = M.edgeSet.ncard := by
    rw [←Set.ncard_coe_finset,SimpleGraph.coe_edgeFinset]
    rw [←M.image_coe_edgeSet_coe]
    exact (Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)).symm
  rw [hc] at h
  have hh (x : M.verts) : M.coe.degree x = 1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    obtain ⟨w,hw,hu⟩ := hM x.property
    refine ⟨⟨w,hw.snd_mem⟩,hw,?_⟩
    intro y hy
    exact Subtype.ext (hu y.val hy)
  have hs : (∑ x : M.verts, M.coe.degree x) = Nat.card M.verts := by
    calc
      _ = ∑ _x : M.verts, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro x _
        convert! hh x
      _ = _ := by simp [Nat.card_eq_fintype_card]
  have hh2 : Nat.card M.verts = 2*M.edgeSet.ncard := by
    calc
      _ = (∑ x : M.verts, M.coe.degree x) := hs.symm
      _ = _ := by convert! h
  simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hh2

end PathsTreesFlowers.Duality.Proof
end
-- END COMPLETE MODULE MatchingCard

-- BEGIN COMPLETE MODULE AugmentRestriction
section

namespace PathsTreesFlowers.Duality.Proof
open SimpleGraph Set
variable {V : Type*} {G : SimpleGraph V} {d : ℕ}

def restrictAugmented (P : (augmented G d).Subgraph) : G.Subgraph where
  verts := {v | ∃ w, P.Adj (.inl v) (.inl w)}
  Adj v w := P.Adj (.inl v) (.inl w)
  adj_sub h := P.adj_sub h
  edge_vert h := ⟨_,h⟩
  symm := ⟨fun _ _ h => h.symm⟩

lemma restrictAugmented_matching {P : (augmented G d).Subgraph} (hP : P.IsMatching) :
    (restrictAugmented P).IsMatching := by
  rintro v ⟨w,hw⟩
  refine ⟨w,hw,?_⟩
  intro z hz
  exact Sum.inl.inj (hP.eq_of_adj_left hz hw)

lemma restrictAugmented_unmatched {P : (augmented G d).Subgraph} (hP : P.IsPerfectMatching)
    {v : V} (hv : v ∉ (restrictAugmented P).verts) : ∃ i : Fin d, P.Adj (.inl v) (.inr i) := by
  obtain ⟨w,hw,_⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP (.inl v)
  cases w with
  | inl u => exact False.elim (hv ⟨u,hw⟩)
  | inr i => exact ⟨i,hw⟩

lemma restrictAugmented_missing_card [Finite V] {P : (augmented G d).Subgraph}
    (hP : P.IsPerfectMatching) : (restrictAugmented P).vertsᶜ.ncard ≤ d := by
  classical
  let f : {v : V // v ∉ (restrictAugmented P).verts} → Fin d :=
    fun v => (restrictAugmented_unmatched hP v.property).choose
  have hf : Function.Injective f := by
    intro v w h
    have hv := (restrictAugmented_unmatched hP v.property).choose_spec
    have hw := (restrictAugmented_unmatched hP w.property).choose_spec
    change P.Adj (.inl v.val) (.inr (f v)) at hv
    change P.Adj (.inl w.val) (.inr (f w)) at hw
    rw [h] at hv
    exact Subtype.ext (Sum.inl.inj (hP.1.eq_of_adj_right hv hw))
  have h := Nat.card_le_card_of_injective f hf
  change Nat.card ↥((restrictAugmented P).vertsᶜ) ≤ Nat.card (Fin d) at h
  simpa only [Nat.card_coe_set_eq, Nat.card_fin] using h

lemma restrictAugmented_card [Finite V] {P : (augmented G d).Subgraph}
    (hP : P.IsPerfectMatching) : Nat.card V ≤ 2*(restrictAugmented P).edgeSet.ncard+d := by
  have h := restrictAugmented_missing_card hP
  have hc := Set.ncard_add_ncard_compl (restrictAugmented P).verts
  rw [matching_vertex_card (restrictAugmented_matching hP.1)] at hc
  omega

end PathsTreesFlowers.Duality.Proof
end
-- END COMPLETE MODULE AugmentRestriction

-- BEGIN COMPLETE MODULE MatchingLowerBound
section

namespace PathsTreesFlowers.Duality.Proof
open SimpleGraph Set
variable {V : Type*} [Finite V]

lemma matching_exists_of_odd_bound (G : SimpleGraph V) (d : ℕ)
    (heven : Even (Nat.card V+d))
    (hbound : ∀ U : Set V, (((⊤ : G.Subgraph).deleteVerts U).coe).oddComponents.ncard ≤ U.ncard+d) :
    ∃ M : G.Subgraph, M.IsMatching ∧ Nat.card V ≤ 2*M.edgeSet.ncard+d := by
  obtain ⟨P,hP⟩ := augmented_tutte G d heven hbound
  exact ⟨restrictAugmented P,restrictAugmented_matching hP.1,restrictAugmented_card hP⟩

end PathsTreesFlowers.Duality.Proof
end
-- END COMPLETE MODULE MatchingLowerBound

-- BEGIN COMPLETE MODULE MatchingRoot
section

namespace PathsTreesFlowers.Duality

theorem matching_duality_theorem {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) :
    ∃ M : Finset E, IsMaxMatching G M ∧
      ∃ S : Finset (Finset V), IsMinOddSetCover G S ∧ M.card = capacitySum S := by
  classical
  let H := Proof.underlying G
  obtain ⟨S,hS⟩ := Proof.exists_max_deficiency H
  obtain ⟨d,hd,heven,hbound⟩ := Proof.deficiency_data H hS
  obtain ⟨M,hM,hcard⟩ := Proof.matching_exists_of_odd_bound H d heven hbound
  obtain ⟨N,hN,hNcard⟩ := Proof.native_matching_of_simple G M hM
  obtain ⟨C,hC,hcap⟩ := Proof.deletion_cover G S
  have hbudget := Proof.component_cover_budget H S
  have hweak := Proof.weak_duality G hN hC
  have hNeq : N.card = capacitySum C := by
    rw [Nat.card_eq_fintype_card] at hcard
    rw [← hNcard] at hcard
    change capacitySum C ≤ S.card + ∑ c : (Proof.residual H S).ConnectedComponent,
      (Proof.componentVertices H S c).card / 2 at hcap
    omega
  refine ⟨N, ⟨hN, ?_⟩, C, ⟨hC, ?_⟩, hNeq⟩
  · intro N' hN'
    exact (Proof.weak_duality G hN' hC).trans_eq hNeq.symm
  · intro C' hC'
    exact hNeq ▸ Proof.weak_duality G hN hC'

end PathsTreesFlowers.Duality

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) :
    ∃ M : Finset E, PathsTreesFlowers.Duality.IsMaxMatching G M ∧
      ∃ S : Finset (Finset V), PathsTreesFlowers.Duality.IsMinOddSetCover G S ∧
        M.card = PathsTreesFlowers.Duality.capacitySum S :=
  PathsTreesFlowers.Duality.matching_duality_theorem G
end
-- END COMPLETE MODULE MatchingRoot
