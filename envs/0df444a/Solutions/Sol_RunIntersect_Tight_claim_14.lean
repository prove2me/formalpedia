-- Prove2me | solution 1 for RunIntersect.Tight.claim_14
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-26T12:12:48.522188+00:00
-- url     : https://prove2.me/submissions/6669d7f2-5114-452a-99f1-e7fbeb6b5deb

import Mathlib
import Definitions.Def_RunIntersect_Tight_Setting

open RunIntersect.Tight

variable {α : Type*} [Fintype α] [DecidableEq α] {G G' : RunIntersect.Tight.Hypergraph α}

/- The same running-intersection datum seen in G: e0, K, ord, u are kept, and the membership
   fields follow from G'.E ⊆ G.E. -/
def ridata_of_subset (G G' : RunIntersect.Tight.Hypergraph α) (hV : G'.V ⊆ G.V) (hE : G'.E ⊆ G.E)
    (d' : RIData G') : RIData G where
  e0 := d'.e0
  K := d'.K
  ord := d'.ord
  u := d'.u
  he0 := hE d'.he0
  hK := by
    intro k hk
    obtain ⟨hne, hkg⟩ := Finset.mem_erase.1 (d'.hK hk)
    exact Finset.mem_erase.2 ⟨hne, hE hkg⟩
  hadj := d'.hadj
  hnodup := d'.hnodup
  hord := d'.hord
  hri := d'.hri
  hu := d'.hu

lemma lhs_ridata_of_subset (G G' : RunIntersect.Tight.Hypergraph α) (hV : G'.V ⊆ G.V) (hE : G'.E ⊆ G.E)
    (d' : RIData G') : (ridata_of_subset G G' hV hE d').lhs = d'.lhs := by
  funext z
  rfl

lemma rhs_ridata_of_subset (G G' : RunIntersect.Tight.Hypergraph α) (hV : G'.V ⊆ G.V) (hE : G'.E ⊆ G.E)
    (d' : RIData G') : (ridata_of_subset G G' hV hE d').rhs = d'.rhs := by
  rfl

lemma restrict_on_coords (H : RunIntersect.Tight.Hypergraph α) (z : α ⊕ Finset α → ℝ) (p) (hp : p ∈ H.coords) :
    restrict H z p = z p := by
  simp_all [restrict]

namespace P2MHole01_b95ecb2f
universe u_1
namespace SolutionAux

variable {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]

/-- A node or an edge of `H` is a coordinate of `H`. -/
lemma inl_in_coords (H : RunIntersect.Tight.Hypergraph α) (v : α) (hv : v ∈ H.V) : Sum.inl v ∈ H.coords := by
  rw [RunIntersect.Tight.Hypergraph.coords, Finset.mem_union]
  left
  rw [Finset.mem_image]
  refine ⟨v, hv, rfl⟩

lemma inr_in_coords (H : RunIntersect.Tight.Hypergraph α) (e : Finset α) (he : e ∈ H.E) : Sum.inr e ∈ H.coords := by
  rw [RunIntersect.Tight.Hypergraph.coords, Finset.mem_union]
  right
  rw [Finset.mem_image]
  refine ⟨e, he, rfl⟩

/-- The foldr-union of a list of sets each of which lies in `W` lies in `W`. -/
lemma foldr_union_subset_of_list (l : List (Finset α)) (W : Finset α)
    (h : ∀ j ∈ l, j ⊆ W) : l.foldr (· ∪ ·) ∅ ⊆ W := by
  induction l with
  | nil => simp [List.foldr_nil]
  | cons x xs ih =>
    rw [List.foldr_cons]
    exact Finset.union_subset (h x List.mem_cons_self)
      (ih (fun j hj => h j (List.mem_cons_of_mem x hj)))

/-- For `l = d'.ord.map (d'.e0 ∩ ·)`, `Nset l i` is contained in `G'.V`: every set of `l`
    lies in `d'.e0 ⊆ G'.V`, so `prefixUnion l i` (a foldr-union of sets of `l`) does. -/
lemma Nset_in_V {G' : RunIntersect.Tight.Hypergraph α} (d' : RIData G') (i : ℕ) :
    Nset (d'.ord.map (d'.e0 ∩ ·)) i ⊆ G'.V := by
  let l := d'.ord.map (d'.e0 ∩ ·)
  have hEe0 : d'.e0 ⊆ G'.V := G'.edge_subset d'.e0 d'.he0
  have helem : ∀ j ∈ l.take i, j ⊆ G'.V := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 (List.mem_of_mem_take hj)
    exact Finset.inter_subset_left.trans hEe0
  calc Nset l i
      ⊆ prefixUnion l i := by
        rw [Nset]
        exact Finset.inter_subset_right
      _ ⊆ G'.V := by
        rw [prefixUnion]
        exact foldr_union_subset_of_list (l.take i) G'.V helem

/-- For a neighbour `k` with nonempty `N(k)`, the node `u k` lies in `G'.V`. -/
lemma u_in_V {G' : RunIntersect.Tight.Hypergraph α} (d' : RIData G') (k : Finset α) (hk : k ∈ d'.K)
    (hN : (d'.N k).Nonempty) : d'.u k ∈ G'.V := by
  exact (Nset_in_V d' (d'.ord.idxOf k)) (d'.hu k hk hN)

end SolutionAux

open SolutionAux

theorem solution {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {G' : RunIntersect.Tight.Hypergraph α} (d' : RIData G') (z : α ⊕ Finset α → ℝ) :
  d'.lhs (restrict G' z) = d'.lhs z := by
  have hKe : d'.K ⊆ G'.E := d'.hK.trans (Finset.erase_subset d'.e0 G'.E)
  have h1 : (∑ k ∈ d'.K.filter (fun k => (d'.N k).Nonempty), (restrict G' z) (Sum.inl (d'.u k))) =
      (∑ k ∈ d'.K.filter (fun k => (d'.N k).Nonempty), z (Sum.inl (d'.u k))) :=
    Finset.sum_congr rfl (fun k hk =>
      restrict_on_coords G' z (Sum.inl (d'.u k))
        (inl_in_coords G' (d'.u k) (u_in_V d' k (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2)))
  have h2 : (∑ v ∈ d'.e0 \ d'.K.biUnion id, (restrict G' z) (Sum.inl v)) =
      (∑ v ∈ d'.e0 \ d'.K.biUnion id, z (Sum.inl v)) :=
    Finset.sum_congr rfl (fun v hv =>
      restrict_on_coords G' z (Sum.inl v)
        (inl_in_coords G' v ((G'.edge_subset d'.e0 d'.he0) (Finset.mem_sdiff.mp hv).1)))
  have h3 : (∑ k ∈ d'.K, (restrict G' z) (Sum.inr k)) = (∑ k ∈ d'.K, z (Sum.inr k)) :=
    Finset.sum_congr rfl (fun k hk =>
      restrict_on_coords G' z (Sum.inr k) (inr_in_coords G' k (hKe hk)))
  have h4 : (restrict G' z) (Sum.inr d'.e0) = z (Sum.inr d'.e0) :=
    restrict_on_coords G' z (Sum.inr d'.e0) (inr_in_coords G' d'.e0 d'.he0)
  dsimp only [RIData.lhs]
  rw [h1, h2, h3, h4]
end P2MHole01_b95ecb2f

/- The support of `lhs d'` (the nodes u k with N(k) ≠ ∅, the nodes of e0 \ ⋃K, the edges K and e0)
   lies in G'.coords, where restrict G' agrees with z. -/
-- riskiest
lemma lhs_restr (d' : RIData G') (z : α ⊕ Finset α → ℝ) :
    d'.lhs (restrict G' z) = d'.lhs z := by
  (first | exact P2MHole01_b95ecb2f.solution d' z | (apply P2MHole01_b95ecb2f.solution <;> assumption))

theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    (G G' : RunIntersect.Tight.Hypergraph α) (hV : G'.V ⊆ G.V) (hE : G'.E ⊆ G.E) :
    (∀ d' : RIData G', ∃ d : RIData G, d.lhs = d'.lhs ∧ d.rhs = d'.rhs) ∧
      ∀ z ∈ MPRI G, restrict G' z ∈ MPRI G' := by
  refine ⟨fun d' => ⟨ridata_of_subset G G' hV hE d',
      lhs_ridata_of_subset G G' hV hE d', rhs_ridata_of_subset G G' hV hE d'⟩, ?_⟩
  intro z hz
  dsimp only [MPRI] at hz ⊢
  obtain ⟨hlp, hri⟩ := hz
  dsimp only [MPLP] at hlp
  have hinl : ∀ v ∈ G'.V, Sum.inl v ∈ G'.coords :=
    fun v hv => Finset.mem_union.2 (Or.inl (Finset.mem_image.2 ⟨v, hv, rfl⟩))
  have hinr : ∀ e ∈ G'.E, Sum.inr e ∈ G'.coords :=
    fun e he => Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨e, he, rfl⟩))
  have hre : ∀ p ∈ G'.coords, restrict G' z p = z p := fun p hp => restrict_on_coords G' z p hp
  refine ⟨?_, ?_⟩
  · constructor
    · intro v hv
      rw [hre (Sum.inl v) (hinl v hv)]
      exact hlp.1 v (hV hv)
    · constructor
      · intro e he
        obtain ⟨h0, hsumle, hvle⟩ := hlp.2.1 e (hE he)
        have hrw : restrict G' z (Sum.inr e) = z (Sum.inr e) := hre (Sum.inr e) (hinr e he)
        have hsum : (∑ v ∈ e, restrict G' z (Sum.inl v)) = ∑ v ∈ e, z (Sum.inl v) :=
          Finset.sum_congr rfl fun v hv => hre (Sum.inl v) (hinl v (G'.edge_subset e he hv))
        refine ⟨?_, ?_, ?_⟩
        · rw [← hrw] at h0
          exact h0
        · rw [hsum, hrw]
          exact hsumle
        · intro v hv
          rw [hrw, hre (Sum.inl v) (hinl v (G'.edge_subset e he hv))]
          exact hvle v hv
      · intro p h
        simp_all [restrict]
  · intro d'
    have hrestr : d'.lhs (restrict G' z) = d'.lhs z := lhs_restr d' z
    have hd : ∃ d : RIData G, d.lhs = d'.lhs ∧ d.rhs = d'.rhs :=
      ⟨ridata_of_subset G G' hV hE d',
        lhs_ridata_of_subset G G' hV hE d', rhs_ridata_of_subset G G' hV hE d'⟩
    obtain ⟨d, hd1, hd2⟩ := hd
    calc
      d'.lhs (restrict G' z) = d'.lhs z := hrestr
      _ = d.lhs z := (congrArg (· z) hd1).symm
      _ ≤ d.rhs := hri d
      _ = d'.rhs := hd2
