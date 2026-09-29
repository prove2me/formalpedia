-- Prove2me | solution 1 for OPG500Counterexample.tight_edge_metric_bridge
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T15:40:10.835713+00:00
-- url     : https://prove2.me/submissions/023791eb-2d6a-4431-94a5-eb20f83ade53

import Definitions.Def_opg500_weighted_cycle_models

open Set
open scoped Sym2

universe u

namespace GeodesicBridge
open OPG500Counterexample
open scoped Classical

variable {V : Type u} {G : SimpleGraph V} (ℓ : EdgeWeight G)

/-- The edge weight extended by zero to all of `Sym2 V`. -/
noncomputable def w (e : Sym2 V) : ℝ := if h : e ∈ G.edgeSet then ℓ ⟨e, h⟩ else 0

lemma w_nonneg (hpos : IsPositive ℓ) (e : Sym2 V) : 0 ≤ w ℓ e := by
  unfold w
  split
  · exact (hpos _).le
  · exact le_rfl

lemma w_apply {e : Sym2 V} (he : e ∈ G.edgeSet) : w ℓ e = ℓ ⟨e, he⟩ := by
  simp [w, he]

lemma weightedLength_eq {x y : V} (p : G.Walk x y) :
    Walk.weightedLength ℓ p = (p.edges.map (w ℓ)).sum := by
  unfold Walk.weightedLength Walk.edgeList
  rw [List.map_map]
  rw [List.map_congr_left
    (g := fun e : {e // e ∈ p.edges} => w ℓ e.1)
    (fun e _ => by simp [w, p.edges_subset_edgeSet e.2])]
  exact congrArg List.sum (List.attach_map_val (f := w ℓ))

end GeodesicBridge

namespace GeodesicBridge
open OPG500Counterexample
open scoped Classical

variable {V : Type u} {G : SimpleGraph V} (ℓ : EdgeWeight G)

lemma list_sum_le_of_sublist {l₁ l₂ : List ℝ} (h : l₁.Sublist l₂) :
    (∀ a ∈ l₂, 0 ≤ a) → l₁.sum ≤ l₂.sum := by
  induction h with
  | slnil => intro _; simp
  | cons a hh ih =>
      intro hnn
      have h1 := ih (fun b hb => hnn b (List.mem_cons_of_mem _ hb))
      have h2 := hnn a List.mem_cons_self
      simp only [List.sum_cons]
      exact h1.trans (le_add_of_nonneg_left h2)
  | cons_cons a hh ih =>
      intro hnn
      have h1 := ih (fun b hb => hnn b (List.mem_cons_of_mem _ hb))
      simp only [List.sum_cons]
      exact add_le_add le_rfl h1

lemma sum_le_of_nodup_subset (hpos : IsPositive ℓ) {l₁ l₂ : List (Sym2 V)}
    (h1 : l₁.Nodup) (h2 : l₁ ⊆ l₂) :
    (l₁.map (w ℓ)).sum ≤ (l₂.map (w ℓ)).sum := by
  obtain ⟨l, hperm, hsub⟩ := List.subperm_of_subset h1 h2
  have h3 : (l.map (w ℓ)).sum = (l₁.map (w ℓ)).sum := (hperm.map (w ℓ)).sum_eq
  rw [← h3]
  refine list_sum_le_of_sublist (hsub.map (w ℓ)) ?_
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  exact w_nonneg ℓ hpos b

lemma wl_append {x y z : V} (p : G.Walk x y) (q : G.Walk y z) :
    Walk.weightedLength ℓ (p.append q)
      = Walk.weightedLength ℓ p + Walk.weightedLength ℓ q := by
  simp [weightedLength_eq, SimpleGraph.Walk.edges_append]

lemma wl_reverse {x y : V} (p : G.Walk x y) :
    Walk.weightedLength ℓ p.reverse = Walk.weightedLength ℓ p := by
  simp [weightedLength_eq, SimpleGraph.Walk.edges_reverse, List.map_reverse]

lemma wl_bypass (hpos : IsPositive ℓ) {x y : V} (p : G.Walk x y) :
    Walk.weightedLength ℓ p.bypass ≤ Walk.weightedLength ℓ p := by
  rw [weightedLength_eq, weightedLength_eq]
  exact sum_le_of_nodup_subset ℓ hpos
    (p.bypass_isPath.isTrail.edges_nodup) (p.edges_bypass_subset_edges)

lemma IsShortest.reverse (hpos : IsPositive ℓ) {x y : V} {p : G.Walk x y}
    (hp : Walk.IsShortest ℓ p) : Walk.IsShortest ℓ p.reverse := by
  refine ⟨hp.1.reverse, ?_⟩
  intro q hq
  rw [wl_reverse]
  have := hp.2 q.reverse hq.reverse
  rwa [wl_reverse] at this

end GeodesicBridge

namespace GeodesicBridge
open OPG500Counterexample
open scoped Classical

variable {V : Type u} {G : SimpleGraph V} (ℓ : EdgeWeight G)

/-- A middle segment of a shortest path is itself shortest. -/
lemma splice (hpos : IsPositive ℓ) {x y u v : V} {p : G.Walk x y}
    (hp : Walk.IsShortest ℓ p)
    (A : G.Walk x u) (m : G.Walk u v) (B : G.Walk v y)
    (hdec : p = A.append (m.append B)) (hm : m.IsPath) :
    Walk.IsShortest ℓ m := by
  refine ⟨hm, ?_⟩
  intro q hq
  by_contra hlt
  rw [not_le] at hlt
  have h1 : Walk.weightedLength ℓ p
      ≤ Walk.weightedLength ℓ (A.append (q.append B)).bypass :=
    hp.2 _ (SimpleGraph.Walk.bypass_isPath _)
  have h2 : Walk.weightedLength ℓ (A.append (q.append B)).bypass
      ≤ Walk.weightedLength ℓ (A.append (q.append B)) := wl_bypass ℓ hpos _
  have h3 : Walk.weightedLength ℓ (A.append (q.append B))
      = Walk.weightedLength ℓ A
        + (Walk.weightedLength ℓ q + Walk.weightedLength ℓ B) := by
    rw [wl_append, wl_append]
  have h4 : Walk.weightedLength ℓ p
      = Walk.weightedLength ℓ A
        + (Walk.weightedLength ℓ m + Walk.weightedLength ℓ B) := by
    rw [hdec, wl_append, wl_append]
  have h5 := h4 ▸ (h1.trans (h2.trans_eq h3))
  have h6 := (add_le_add_iff_left (Walk.weightedLength ℓ A)).mp h5
  have h7 := (add_le_add_iff_right (Walk.weightedLength ℓ B)).mp h6
  exact absurd h7 (not_le.mpr hlt)

/-- Every edge of a walk splits it into a prefix, that edge, and a suffix. -/
lemma split_edge {x y : V} (p : G.Walk x y) :
    ∀ {e : Sym2 V}, e ∈ p.edges →
      ∃ (c d : V) (hcd : G.Adj c d) (p1 : G.Walk x c) (p2 : G.Walk d y),
        s(c, d) = e ∧ p = p1.append (SimpleGraph.Walk.cons hcd p2) := by
  induction p with
  | nil => intro e he; simp at he
  | cons h p' ih =>
      intro e he
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨_, _, h, SimpleGraph.Walk.nil, p', rfl, by simp⟩
      · obtain ⟨c, d, hcd, p1, p2, hce, hdec⟩ := ih he
        exact ⟨c, d, hcd, SimpleGraph.Walk.cons h p1, p2, hce, by rw [hdec]; simp⟩

end GeodesicBridge

namespace GeodesicBridge
open OPG500Counterexample
open scoped Classical

variable {V : Type u} {G : SimpleGraph V} (ℓ : EdgeWeight G)

/-- Every edge on a shortest path is tight. -/
lemma tight_of_mem_edges (hpos : IsPositive ℓ) {x y : V} {p : G.Walk x y}
    (hp : Walk.IsShortest ℓ p) {e : Sym2 V} (he : e ∈ p.edges) :
    Edge.IsTight ℓ ⟨e, p.edges_subset_edgeSet he⟩ := by
  obtain ⟨c, d, hcd, p1, p2, hce, hdec⟩ := split_edge p he
  have hdec' : p = p1.append (hcd.toWalk.append p2) := by
    rw [hdec]; rfl
  exact ⟨c, d, hcd, hce.symm, splice ℓ hpos hp p1 _ p2 hdec' hcd.isPath_toWalk⟩

/-- In a finite connected graph a shortest path exists between any two vertices. -/
lemma exists_shortest [Fintype V] [DecidableEq V] (hconn : G.Connected) (x y : V) :
    ∃ p : G.Walk x y, Walk.IsShortest ℓ p := by
  classical
  have hne : (Finset.univ : Finset (G.Path x y)).Nonempty := by
    obtain ⟨q⟩ := hconn x y
    exact ⟨⟨q.bypass, q.bypass_isPath⟩, Finset.mem_univ _⟩
  obtain ⟨P, -, hP⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (G.Path x y))
      (fun P => Walk.weightedLength ℓ P.1) hne
  exact ⟨P.1, P.2, fun q hq => hP ⟨q, hq⟩ (Finset.mem_univ _)⟩

end GeodesicBridge

namespace GeodesicBridge
open OPG500Counterexample
open scoped Classical

variable {V : Type u} {G : SimpleGraph V} (ℓ : EdgeWeight G)

/-- Between any two vertices of a shortest path there is a shortest path
whose edges all lie on the given one. -/
lemma exists_shortest_sub (hpos : IsPositive ℓ) {x y : V} {p : G.Walk x y}
    (hp : Walk.IsShortest ℓ p) {u v : V} (hu : u ∈ p.support) (hv : v ∈ p.support) :
    ∃ r : G.Walk u v, Walk.IsShortest ℓ r ∧ r.edges ⊆ p.edges := by
  classical
  by_cases hvD : v ∈ (p.dropUntil u hu).support
  · refine ⟨(p.dropUntil u hu).takeUntil v hvD, ?_, ?_⟩
    · refine splice ℓ hpos hp (p.takeUntil u hu) _
        ((p.dropUntil u hu).dropUntil v hvD) ?_ ((hp.1.dropUntil hu).takeUntil hvD)
      rw [(p.dropUntil u hu).take_spec hvD, p.take_spec hu]
    · intro e he
      have h1 := (p.dropUntil u hu).edges_takeUntil_subset_edges hvD he
      have h2 := p.edges_dropUntil_subset_edges hu h1
      exact h2
  · have hvA : v ∈ (p.takeUntil u hu).support := by
      have h := hv
      rw [← p.take_spec hu, SimpleGraph.Walk.support_append, List.mem_append] at h
      rcases h with h | h
      · exact h
      · exact absurd (List.mem_of_mem_tail h) hvD
    have hs : Walk.IsShortest ℓ ((p.takeUntil u hu).dropUntil v hvA) := by
      refine splice ℓ hpos hp ((p.takeUntil u hu).takeUntil v hvA) _
        (p.dropUntil u hu) ?_ ((hp.1.takeUntil hu).dropUntil hvA)
      rw [SimpleGraph.Walk.append_assoc, (p.takeUntil u hu).take_spec hvA, p.take_spec hu]
    refine ⟨((p.takeUntil u hu).dropUntil v hvA).reverse,
      IsShortest.reverse ℓ hpos hs, ?_⟩
    intro e he
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    exact p.edges_takeUntil_subset_edges hu
      ((p.takeUntil u hu).edges_dropUntil_subset_edges hvA he)

end GeodesicBridge

open OPG500Counterexample GeodesicBridge in
theorem solution
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconnected : G.Connected)
    (ℓ : EdgeWeight G) (hpositive : IsPositive ℓ) :
    (∀ x y : V,
      ∃ p : G.Walk x y,
        Walk.IsShortest ℓ p ∧
          ∀ e (he : e ∈ p.edges), Edge.IsTight ℓ ⟨e, p.edges_subset_edgeSet he⟩) ∧
    (∀ e : Edge G, ¬ Edge.IsTight ℓ e →
      ∃ x y : V, ∃ h : G.Adj x y, ∃ p : G.Walk x y, ∃ C : Cycle G,
        e.1 = s(x, y) ∧ Walk.IsShortest ℓ p ∧ C.IsGeodesic ℓ ∧
          C.edgeSet = insert e.1 p.edgeSet) := by
  classical
  constructor
  · intro x y
    obtain ⟨p, hp⟩ := exists_shortest ℓ hconnected x y
    exact ⟨p, hp, fun e he => tight_of_mem_edges ℓ hpositive hp he⟩
  · rintro ⟨z, hz⟩ hnt
    induction z using Sym2.ind with
    | _ x y =>
      have hxy : G.Adj x y := hz
      obtain ⟨p, hp⟩ := exists_shortest ℓ hconnected x y
      -- the edge is not tight, so some path beats it
      have hex : ∃ q : G.Walk x y, q.IsPath ∧
          Walk.weightedLength ℓ q < Walk.weightedLength ℓ hxy.toWalk := by
        by_contra hc
        refine hnt ⟨x, y, hxy, rfl, hxy.isPath_toWalk, ?_⟩
        intro q hq
        by_contra hlt
        exact hc ⟨q, hq, not_le.mp hlt⟩
      obtain ⟨q, hq, hqlt⟩ := hex
      have hedge : Walk.weightedLength ℓ hxy.toWalk = w ℓ s(x, y) := by
        rw [weightedLength_eq, hxy.edges_toWalk]
        simp
      have hkey : Walk.weightedLength ℓ p < w ℓ s(x, y) :=
        lt_of_le_of_lt (hp.2 q hq) (hedge ▸ hqlt)
      have hnotmem : s(x, y) ∉ p.edges := by
        intro hmem
        have h1 : ([s(x, y)].map (w ℓ)).sum ≤ (p.edges.map (w ℓ)).sum :=
          sum_le_of_nodup_subset ℓ hpositive (List.nodup_singleton _)
            (by intro a ha; rw [List.mem_singleton] at ha; exact ha ▸ hmem)
        rw [weightedLength_eq] at hkey
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h1
        exact absurd h1 (not_le.mpr hkey)
      have hcyc : (SimpleGraph.Walk.cons hxy p.reverse).IsCycle := by
        rw [SimpleGraph.Walk.cons_isCycle_iff]
        refine ⟨hp.1.reverse, ?_⟩
        rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]
        exact hnotmem
      refine ⟨x, y, hxy, p, ⟨x, SimpleGraph.Walk.cons hxy p.reverse, hcyc⟩, rfl, hp, ?_, ?_⟩
      · intro a b ha hb
        have hmem : ∀ c : V, c ∈ (SimpleGraph.Walk.cons hxy p.reverse).support →
            c ∈ p.support := by
          intro c hc
          rw [SimpleGraph.Walk.support_cons, List.mem_cons,
            SimpleGraph.Walk.support_reverse, List.mem_reverse] at hc
          rcases hc with rfl | hc
          · exact p.start_mem_support
          · exact hc
        obtain ⟨r, hr, hrsub⟩ :=
          exists_shortest_sub ℓ hpositive hp (hmem a ha) (hmem b hb)
        refine ⟨r, hr, ?_⟩
        intro e he
        have : e ∈ p.edges := hrsub he
        simp only [Cycle.edgeSet, SimpleGraph.Walk.edgeSet, Set.mem_ofPred_eq,
          SimpleGraph.Walk.edges_cons, List.mem_cons, SimpleGraph.Walk.edges_reverse,
          List.mem_reverse]
        exact Or.inr this
      · ext e
        simp only [Cycle.edgeSet, SimpleGraph.Walk.edgeSet, Set.mem_ofPred_eq,
          SimpleGraph.Walk.edges_cons, List.mem_cons, SimpleGraph.Walk.edges_reverse,
          List.mem_reverse, Set.mem_insert_iff]

