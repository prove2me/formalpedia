-- Prove2me | solution 1 for StableMSR.Recovery.DecompositionSearch.tight_block_progress
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-14T17:22:07.37267+00:00
-- url     : https://prove2.me/submissions/589567b4-6a92-4fbb-abd4-af0cddfb5767

import Definitions.Def_StableMSR_TightBlockSearch
import Definitions.Def_SeymourThomas1993_Brambles
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Tauto
set_option autoImplicit false
open scoped Classical
namespace StableMSR.Recovery.TreeHelly

/-- A set contains the unique tree path between any two of its vertices. -/
def PathConvex {T : Type} (tree : SimpleGraph T) (C : Finset T) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ p : tree.Walk x y, p.IsPath → ∀ z ∈ p.support, z ∈ C

lemma leaf_neighbor_mem {T : Type} [Fintype T] [DecidableEq T]
    (tree : SimpleGraph T) (htree : tree.IsTree) {v w : T}
    (hadj : tree.Adj v w) (huniq : ∀ u, tree.Adj v u → u = w)
    (C : Finset T) (hc : PathConvex tree C) (hv : v ∈ C) (hC : C ≠ {v}) :
    w ∈ C := by
  classical
  obtain ⟨x, hx, hxv⟩ : ∃ x ∈ C, x ≠ v := by
    by_contra hn
    apply hC
    ext x
    simp only [Finset.mem_singleton]
    constructor
    · intro hx
      by_contra hne
      exact hn ⟨x, hx, hne⟩
    · rintro rfl
      exact hv
  obtain ⟨p, hp⟩ := htree.connected.exists_isPath v x
  have hnil : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hxv.symm
  have hw : p.snd = w := huniq _ (p.adj_snd hnil)
  exact hw ▸ hc v hv x hx p hp p.snd (List.mem_of_mem_tail (p.snd_mem_tail_support hnil))

/-- The Helly property for arbitrary families of nonempty path-convex subsets
of a finite tree. The index type need not be finite. -/
theorem finite_tree_helly {T : Type} [Fintype T] [DecidableEq T]
    (tree : SimpleGraph T) (htree : tree.IsTree) {I : Type*}
    (C : I → Finset T) (hne : ∀ i, (C i).Nonempty)
    (hconv : ∀ i, PathConvex tree (C i))
    (hpair : ∀ i j, ((C i) ∩ (C j)).Nonempty) :
    ∃ t : T, ∀ i, t ∈ C i := by
  classical
  have aux : ∀ n : ℕ, ∀ (T : Type) [Fintype T] [DecidableEq T],
      Fintype.card T = n → ∀ (tree : SimpleGraph T), tree.IsTree →
      ∀ (C : I → Finset T), (∀ i, (C i).Nonempty) →
      (∀ i, PathConvex tree (C i)) →
      (∀ i j, ((C i) ∩ (C j)).Nonempty) → ∃ t : T, ∀ i, t ∈ C i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T _ _ hcard tree ht C hne hc hp
      by_cases hsub : Subsingleton T
      · obtain ⟨t⟩ := ht.connected.nonempty
        refine ⟨t, ?_⟩
        intro i
        obtain ⟨x, hx⟩ := hne i
        exact (hsub.elim x t) ▸ hx
      · letI : Nontrivial T := not_subsingleton_iff_nontrivial.mp hsub
        obtain ⟨v, hvdeg⟩ := ht.exists_vert_degree_one_of_nontrivial
        obtain ⟨w, hvw, hw⟩ := tree.degree_eq_one_iff_existsUnique_adj.mp hvdeg
        by_cases hsing : ∃ i, C i = {v}
        · obtain ⟨i, hi⟩ := hsing
          refine ⟨v, ?_⟩
          intro j
          obtain ⟨x, hx⟩ := hp i j
          obtain ⟨hxi, hxj⟩ := Finset.mem_inter.mp hx
          rw [hi, Finset.mem_singleton] at hxi
          exact hxi ▸ hxj
        · have hnot : ∀ i, C i ≠ {v} := by simpa only [not_exists] using hsing
          let U : Set T := {v}ᶜ
          let tree' := tree.induce U
          have ht' : tree'.IsTree :=
            ⟨ht.connected.induce_compl_singleton_of_degree_eq_one hvdeg, ht.isAcyclic.induce U⟩
          let C' : I → Finset U := fun i => Finset.univ.filter (fun x => x.val ∈ C i)
          have hne' : ∀ i, (C' i).Nonempty := by
            intro i
            obtain ⟨x, hx⟩ := hne i
            by_cases hxv : x = v
            · have hvC : v ∈ C i := hxv ▸ hx
              have hwC := leaf_neighbor_mem tree ht hvw hw (C i) (hc i) hvC (hnot i)
              refine ⟨⟨w, ?_⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwC⟩⟩
              exact fun heq => tree.ne_of_adj hvw heq.symm
            · exact ⟨⟨x, hxv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
          have hc' : ∀ i, PathConvex tree' (C' i) := by
            intro i x hx y hy p hpath z hz
            have hxC := (Finset.mem_filter.mp hx).2
            have hyC := (Finset.mem_filter.mp hy).2
            let f : tree' →g tree := {toFun := Subtype.val, map_rel' := by intro x y h; exact h}
            have hpath' : (p.map f).IsPath := hpath.map Subtype.val_injective
            have hz' : z.val ∈ (p.map f).support := by
              rw [SimpleGraph.Walk.support_map]
              exact List.mem_map.mpr ⟨z, hz, rfl⟩
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc i x.val hxC y.val hyC
              (p.map f) hpath' z.val hz'⟩
          have hp' : ∀ i j, (C' i ∩ C' j).Nonempty := by
            intro i j
            obtain ⟨x, hx⟩ := hp i j
            obtain ⟨hxi, hxj⟩ := Finset.mem_inter.mp hx
            by_cases hxv : x = v
            · have hi := leaf_neighbor_mem tree ht hvw hw (C i) (hc i) (hxv ▸ hxi) (hnot i)
              have hj := leaf_neighbor_mem tree ht hvw hw (C j) (hc j) (hxv ▸ hxj) (hnot j)
              exact ⟨⟨w, fun heq => tree.ne_of_adj hvw heq.symm⟩,
                Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩,
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩⟩
            · exact ⟨⟨x, hxv⟩, Finset.mem_inter.mpr
                ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩,
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxj⟩⟩⟩
          have hlt : Fintype.card U < n := by
            rw [← hcard]
            exact Fintype.card_subtype_lt (x := v) (by simp [U])
          obtain ⟨t, htC⟩ := ih (Fintype.card U) hlt U rfl tree' ht' C' hne' hc' hp'
          exact ⟨t.val, fun i => (Finset.mem_filter.mp (htC i)).2⟩
  exact aux (Fintype.card T) T rfl tree htree C hne hconv hpair

end StableMSR.Recovery.TreeHelly
namespace StableMSR.Recovery.HavenTreewidthObstruction
open Havens TreeHelly RobertsonSeymour1986.GM5
lemma lift_connected_walk {V T : Type} [DecidableEq V] [DecidableEq T]
    (G : SimpleGraph V) (tree : SimpleGraph T) (bags : T → Finset V)
    (htd : IsTreeDecomposition G tree bags) {C : Finset V} {u v : V}
    (p : G.Walk u v) (hp : ∀ z ∈ p.support, z ∈ C)
    (s t : T) (hs : u ∈ bags s) (ht : v ∈ bags t) :
    ∃ q : tree.Walk s t, ∀ z ∈ q.support, ∃ c ∈ C, c ∈ bags z := by
  induction p generalizing s with
  | nil =>
    obtain ⟨q,hq⟩ := htd.1.connected.exists_isPath s t
    refine ⟨q,?_⟩
    intro z hz
    exact ⟨_, hp _ (by simp), htd.2.2.2 s z t q hq hz (Finset.mem_inter.mpr ⟨hs,ht⟩)⟩
  | @cons u v w huv p ih =>
    obtain ⟨b,hbu,hbv⟩ := htd.2.2.1 u v huv
    obtain ⟨q,hq⟩ := htd.1.connected.exists_isPath s b
    have htail : ∀ z ∈ p.support, z ∈ C := by
      intro z hz; exact hp z (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hz)
    obtain ⟨r,hr⟩ := ih htail b hbv ht
    refine ⟨q.append r,?_⟩
    intro z hz
    have hz' : z ∈ q.support ∨ z ∈ r.support := by
      exact (SimpleGraph.Walk.mem_support_append_iff q r).mp hz
    rcases hz' with hzq | hzr
    · exact ⟨u,hp u (by simp),htd.2.2.2 s z b q hq hzq (Finset.mem_inter.mpr ⟨hs,hbu⟩)⟩
    · exact hr z hzr

noncomputable def bagSupport {V T : Type} [DecidableEq V] [Fintype T]
    (bags : T → Finset V) (C : Finset V) : Finset T :=
  Finset.univ.filter (fun t => ∃ c ∈ C, c ∈ bags t)

lemma bagSupport_nonempty {V T : Type} [DecidableEq V] [Fintype T]
    {G : SimpleGraph V} {tree : SimpleGraph T} {bags : T → Finset V}
    (htd : IsTreeDecomposition G tree bags) {C : Finset V} (hC : C.Nonempty) :
    (bagSupport bags C).Nonempty := by
  classical
  obtain ⟨v,hv⟩ := hC
  obtain ⟨t,ht⟩ := htd.2.1 v
  exact ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,v,hv,ht⟩⟩

lemma bagSupport_convex {V T : Type} [DecidableEq V] [Fintype T] [DecidableEq T]
    {G : SimpleGraph V} {tree : SimpleGraph T} {bags : T → Finset V}
    (htd : IsTreeDecomposition G tree bags) {C : Finset V} (hC : ConnectedSet G C) :
    PathConvex tree (bagSupport bags C) := by
  classical
  intro s hs t ht p hp z hz
  obtain ⟨u,hu,hbu⟩ := (Finset.mem_filter.mp hs).2
  obtain ⟨v,hv,hbv⟩ := (Finset.mem_filter.mp ht).2
  obtain ⟨q,hq⟩ := hC.2 u hu v hv
  obtain ⟨r,hr⟩ := lift_connected_walk G tree bags htd q hq s t hbu hbv
  have he := htd.1.isAcyclic.subsingleton_path s t |>.elim ⟨p,hp⟩ r.toPath
  have hpR : p = r.toPath.val := congrArg Subtype.val he
  have hzR : z ∈ r.support := by
    rw [hpR] at hz
    exact r.support_toPath_subset_support hz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr z hzR⟩

end StableMSR.Recovery.HavenTreewidthObstruction

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.DecompositionSearch
open RobertsonSeymour1986.GM5 Havens TreeHelly HavenTreewidthObstruction

/-- If a connected region touches every vertex of a boundary already contained
in one bag, some bag contains the entire boundary and advances into the region. -/
theorem boundary_advancing_bag {V T : Type} [DecidableEq V] [Fintype T] [DecidableEq T]
    {G : SimpleGraph V} {tree : SimpleGraph T} {bags : T → Finset V}
    (htd : IsTreeDecomposition G tree bags) (S C : Finset V)
    (hC : ConnectedSet G C) (hroot : ∃ r, S ⊆ bags r)
    (htouch : ∀ s ∈ S, ∃ c ∈ C, G.Adj s c) :
    ∃ t, S ⊆ bags t ∧ ∃ c ∈ C, c ∈ bags t := by
  classical
  obtain ⟨root,hroot⟩ := hroot
  let F : Option ↥S → Finset T
    | none => bagSupport bags C
    | some s => Finset.univ.filter (fun t => s.val ∈ bags t)
  have hne : ∀ i, (F i).Nonempty := by
    intro i
    cases i with
    | none => exact bagSupport_nonempty htd hC.1
    | some s => exact ⟨root,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hroot s.property⟩⟩
  have hconv : ∀ i, PathConvex tree (F i) := by
    intro i
    cases i with
    | none => exact bagSupport_convex htd hC
    | some s =>
      intro x hx y hy p hp z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,htd.2.2.2 x z y p hp hz
        (Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hx).2,(Finset.mem_filter.mp hy).2⟩)⟩
  have hedge (s : ↥S) : (F none ∩ F (some s)).Nonempty := by
    obtain ⟨c,hc,hsc⟩ := htouch s.val s.property
    obtain ⟨t,hs,htc⟩ := htd.2.2.1 s.val c hsc
    exact ⟨t,Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,c,hc,htc⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩⟩⟩
  have hpair : ∀ i j, (F i ∩ F j).Nonempty := by
    intro i j
    cases i with
    | none =>
      cases j with
      | none => simpa only [Finset.inter_self] using hne none
      | some s => exact hedge s
    | some s =>
      cases j with
      | none => simpa only [Finset.inter_comm] using hedge s
      | some r =>
        exact ⟨root,Finset.mem_inter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hroot s.property⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _,hroot r.property⟩⟩⟩
  obtain ⟨t,ht⟩ := finite_tree_helly tree htd.1 F hne hconv hpair
  refine ⟨t,?_,(Finset.mem_filter.mp (ht none)).2⟩
  intro s hs
  exact (Finset.mem_filter.mp (ht (some ⟨s,hs⟩))).2

/-- At width w, a tight nonempty region has a progress bag, boundary size at
most w, and a strictly smaller remainder after that bag is removed. -/
theorem boundary_advancing_bag_bound {V T : Type} [DecidableEq V]
    [Fintype T] [DecidableEq T] {G : SimpleGraph V} {tree : SimpleGraph T}
    {bags : T → Finset V} (htd : IsTreeDecomposition G tree bags)
    (S C : Finset V) (w : ℕ) (hC : ConnectedSet G C) (hdisj : Disjoint S C)
    (hroot : ∃ r, S ⊆ bags r) (htouch : ∀ s ∈ S, ∃ c ∈ C, G.Adj s c)
    (hwidth : ∀ t, (bags t).card ≤ w+1) :
    ∃ t, S ⊆ bags t ∧ (∃ c ∈ C, c ∈ bags t) ∧
      S.card ≤ w ∧ (C \ bags t).card < C.card := by
  classical
  obtain ⟨t,hS,c,hc,hct⟩ := boundary_advancing_bag htd S C hC hroot htouch
  have hn : c ∉ S := fun hs => Finset.disjoint_left.mp hdisj hs hc
  have hsize := (Finset.card_le_card (show insert c S ⊆ bags t from
    Finset.insert_subset hct hS)).trans (hwidth t)
  rw [Finset.card_insert_of_notMem hn] at hsize
  refine ⟨t,hS,⟨c,hc,hct⟩,by omega,?_⟩
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.sdiff_subset,?_⟩
  intro he
  have hmem : c ∈ C \ bags t := he.symm ▸ hc
  exact (Finset.mem_sdiff.mp hmem).2 hct

end StableMSR.Recovery.DecompositionSearch
open StableMSR.Recovery.DecompositionSearch RobertsonSeymour1986.GM5 StableMSR.Recovery.Havens
/-- A progress bag may be restricted to the current region and its boundary;
thus all candidates lie in a finite powerset of the current block. -/
theorem StableMSR.Recovery.DecompositionSearch.exists_progress_bag {V T : Type} [DecidableEq V]
    [Fintype T] [DecidableEq T] {G : SimpleGraph V} {tree : SimpleGraph T}
    {bags : T → Finset V} (htd : IsTreeDecomposition G tree bags)
    (S C : Finset V) (w : ℕ) (hC : ConnectedSet G C) (hdisj : Disjoint S C)
    (hroot : ∃ r, S ⊆ bags r) (htouch : ∀ s ∈ S, ∃ c ∈ C, G.Adj s c)
    (hwidth : ∀ t, (bags t).card ≤ w+1) :
    ∃ B : Finset V, S ⊆ B ∧ B ⊆ S ∪ C ∧ B.card ≤ w+1 ∧
      (B ∩ C).Nonempty ∧ S.card ≤ w ∧ (C \ B).card < C.card := by
  classical
  obtain ⟨t,hS,⟨c,hc,hct⟩,hcard,hsmall⟩ :=
    boundary_advancing_bag_bound htd S C w hC hdisj hroot htouch hwidth
  let B := bags t ∩ (S ∪ C)
  have hCB : C \ B = C \ bags t := by
    ext v
    simp only [B,Finset.mem_sdiff,Finset.mem_inter,Finset.mem_union]
    tauto
  refine ⟨B,?_,Finset.inter_subset_right,
    (Finset.card_le_card Finset.inter_subset_left).trans (hwidth t),?_,hcard,?_⟩
  · intro s hs
    exact Finset.mem_inter.mpr ⟨hS hs,Finset.mem_union_left _ hs⟩
  · exact ⟨c,Finset.mem_inter.mpr
      ⟨Finset.mem_inter.mpr ⟨hct,Finset.mem_union_right _ hc⟩,hc⟩⟩
  · simpa only [hCB] using hsmall

namespace StableMSR.Recovery.Havens
variable {V : Type} [DecidableEq V]
lemma mem_of_walk_closed {G : SimpleGraph V} {C D : Finset V}
    (hclosed : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ D → y ∈ C)
    {u v : V} (p : G.Walk u v) (hu : u ∈ C)
    (hp : ∀ z ∈ p.support, z ∈ D) : v ∈ C := by
  induction p with
  | nil => exact hu
  | @cons u v w huv p ih =>
    apply ih (hclosed u hu v huv (hp v (by simp)))
    intro z hz
    exact hp z (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons]; exact Or.inr hz)

lemma flap_contains_touching {G : SimpleGraph V} {W C D : Finset V}
    (hC : IsFlap G W C) (hD : ConnectedSet G D)
    (havoid : Disjoint W D) (htouch : Touch G C D) : D ⊆ C := by
  obtain ⟨u, huD, huC⟩ : ∃ u, u ∈ D ∧ u ∈ C := by
    rcases htouch with ⟨u, huC, huD⟩ | ⟨x, hx, y, hy, hxy⟩
    · exact ⟨u, huD, huC⟩
    · exact ⟨y, hy, hC.closed x hx y hxy (fun hyW =>
        Finset.disjoint_left.mp havoid hyW hy)⟩
  intro v hv
  obtain ⟨p, hp⟩ := hD.2 u huD v hv
  exact mem_of_walk_closed (fun x hx y hxy hy =>
    hC.closed x hx y hxy (fun hyW => Finset.disjoint_left.mp havoid hyW hy)) p huC hp

noncomputable def componentWithin (G : SimpleGraph V) (U : Finset V) (u : V) : Finset V :=
  by classical exact U.filter (fun v => ∃ p : G.Walk u v, ∀ z ∈ p.support, z ∈ U)

lemma mem_componentWithin {G : SimpleGraph V} {U : Finset V} {u v : V} :
    v ∈ componentWithin G U u ↔ v ∈ U ∧ ∃ p : G.Walk u v, ∀ z ∈ p.support, z ∈ U := by
  classical
  simp only [componentWithin, Finset.mem_filter]

lemma componentWithin_subset (G : SimpleGraph V) (U : Finset V) (u : V) :
    componentWithin G U u ⊆ U := by
  intro v hv
  exact (mem_componentWithin.mp hv).1

lemma self_mem_componentWithin {G : SimpleGraph V} {U : Finset V} {u : V} (hu : u ∈ U) :
    u ∈ componentWithin G U u := by
  refine mem_componentWithin.mpr ⟨hu, .nil, ?_⟩
  simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using fun z (hz : z = u) => hz ▸ hu

lemma support_subset_componentWithin {G : SimpleGraph V} {U : Finset V}
    {u v : V} (p : G.Walk u v) (hp : ∀ z ∈ p.support, z ∈ U) :
    ∀ z ∈ p.support, z ∈ componentWithin G U u := by
  intro z hz
  refine mem_componentWithin.mpr ⟨hp z hz, p.takeUntil z hz, ?_⟩
  intro w hw
  exact hp w (p.support_takeUntil_subset_support hz hw)

lemma componentWithin_connected {G : SimpleGraph V} {U : Finset V} {u : V} (hu : u ∈ U) :
    ConnectedSet G (componentWithin G U u) := by
  refine ⟨⟨u, self_mem_componentWithin hu⟩, ?_⟩
  intro x hx y hy
  obtain ⟨_, p, hp⟩ := mem_componentWithin.mp hx
  obtain ⟨_, q, hq⟩ := mem_componentWithin.mp hy
  refine ⟨p.reverse.append q, ?_⟩
  intro z hz
  rcases (SimpleGraph.Walk.mem_support_append_iff p.reverse q).mp hz with hz | hz
  · apply support_subset_componentWithin p hp z
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
  · exact support_subset_componentWithin q hq z hz

lemma componentWithin_closed {G : SimpleGraph V} {U : Finset V} {u x y : V}
    (hx : x ∈ componentWithin G U u) (hxy : G.Adj x y) (hy : y ∈ U) :
    y ∈ componentWithin G U u := by
  obtain ⟨_, p, hp⟩ := mem_componentWithin.mp hx
  refine mem_componentWithin.mpr ⟨hy, p.concat hxy, ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_concat] at hz
  rcases List.mem_append.mp hz with hz | hz
  · exact hp z hz
  · simpa only [List.mem_singleton] using (show z = y from List.mem_singleton.mp hz) ▸ hy

end StableMSR.Recovery.Havens
namespace StableMSR.Recovery.PartialDecompositions
open Havens
variable {V : Type} [Fintype V] [DecidableEq V]
lemma component_exists (G : SimpleGraph V) (S : Finset V) {v : V} (hv : v ∉ S) :
    ∃ C ∈ components G S, v ∈ C := by
  refine ⟨componentWithin G Sᶜ v, mem_components.mpr ⟨componentWithin_connected (Finset.mem_compl.mpr hv), ?_, ?_⟩,
    self_mem_componentWithin (Finset.mem_compl.mpr hv)⟩
  · exact Finset.disjoint_left.mpr (fun x hx hC =>
      (Finset.mem_compl.mp (componentWithin_subset G Sᶜ v hC)) hx)
  · intro x hx y hxy hy
    exact componentWithin_closed hx hxy (Finset.mem_compl.mpr hy)
lemma components_eq_of_mem {G : SimpleGraph V} {S C D : Finset V}
    (hC : C ∈ components G S) (hD : D ∈ components G S)
    {v : V} (hvC : v ∈ C) (hvD : v ∈ D) : C = D := by
  have c := mem_components.mp hC
  have d := mem_components.mp hD
  exact Finset.Subset.antisymm
    (flap_contains_touching d c.connected c.avoids (.inl ⟨v,hvD,hvC⟩))
    (flap_contains_touching c d.connected d.avoids (.inl ⟨v,hvC,hvD⟩))
end StableMSR.Recovery.PartialDecompositions
open scoped BigOperators
namespace StableMSR.Recovery.DecompositionSearch
open Havens PartialDecompositions
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The external vertex boundary, computed in the original graph. -/
lemma boundary_disjoint (G : SimpleGraph V) (C : Finset V) :
    Disjoint (boundary G C) C := by
  exact Finset.disjoint_left.mpr (fun _ hv hc => (mem_boundary.mp hv).1 hc)

lemma boundary_subset {G : SimpleGraph V} {S C : Finset V} (hC : IsFlap G S C) :
    boundary G C ⊆ S := by
  intro v hv
  obtain ⟨hn,u,hu,hadj⟩ := mem_boundary.mp hv
  by_contra hvS
  exact hn (hC.closed u hu v hadj hvS)

/-- Replacing a separator by the exact boundary keeps the same component. -/
lemma flap_at_boundary {G : SimpleGraph V} {S C : Finset V} (hC : IsFlap G S C) :
    IsFlap G (boundary G C) C := by
  refine ⟨hC.connected,boundary_disjoint G C,?_⟩
  intro u hu v huv hv
  by_contra hn
  exact hv (mem_boundary.mpr ⟨hn,u,hu,huv⟩)

/-- The recursive interiors after choosing a bag B in a current interior C. -/
lemma children_disjoint {G : SimpleGraph V} {B C D E : Finset V}
    (hD : D ∈ children G B C) (hE : E ∈ children G B C) (hne : D ≠ E) :
    Disjoint D E := by
  apply Finset.disjoint_left.mpr
  intro v hvD hvE
  exact hne (components_eq_of_mem (mem_components.mpr (mem_children.mp hD).1)
    (mem_components.mpr (mem_children.mp hE).1) hvD hvE)

theorem children_partition {G : SimpleGraph V} {S C B : Finset V}
    (hC : IsFlap G S C) (hSB : S ⊆ B) :
    (children G B C).biUnion id = C \ B := by
  classical
  ext v
  simp only [Finset.mem_biUnion,id_eq,Finset.mem_sdiff]
  constructor
  · rintro ⟨D,hD,hvD⟩
    obtain ⟨hf,hDC⟩ := mem_children.mp hD
    exact ⟨hDC hvD,fun hvB => Finset.disjoint_left.mp hf.avoids hvB hvD⟩
  · rintro ⟨hvC,hvB⟩
    obtain ⟨D,hD,hvD⟩ := component_exists G B hvB
    have hf := mem_components.mp hD
    have havoid : Disjoint S D := Finset.disjoint_left.mpr
      (fun x hxS hxD => Finset.disjoint_left.mp hf.avoids (hSB hxS) hxD)
    have hDC : D ⊆ C := flap_contains_touching hC hf.connected havoid (.inl ⟨v,hvC,hvD⟩)
    exact ⟨D,mem_children.mpr ⟨hf,hDC⟩,hvD⟩

/-- Every chosen vertex is charged once and child interiors partition the remainder. -/
theorem children_card_accounting {G : SimpleGraph V} {S C B : Finset V}
    (hC : IsFlap G S C) (hSB : S ⊆ B) :
    (B ∩ C).card + ∑ D ∈ children G B C, D.card = C.card := by
  classical
  have hs : (∑ D ∈ children G B C, D.card) = (C \ B).card := by
    rw [←Finset.card_biUnion (fun D hD E hE hne => children_disjoint hD hE hne)]
    change ((children G B C).biUnion id).card = (C \ B).card
    rw [children_partition hC hSB]
  rw [hs,Finset.inter_comm]
  exact Finset.card_inter_add_card_sdiff C B

theorem children_strictly_smaller {G : SimpleGraph V} {S C B : Finset V}
    (hC : IsFlap G S C) (hSB : S ⊆ B) (hprogress : (B ∩ C).Nonempty) :
    (∑ D ∈ children G B C, D.card) < C.card ∧
      ∀ D ∈ children G B C, D.card < C.card := by
  have ha := children_card_accounting hC hSB
  have hp := Finset.card_pos.mpr hprogress
  have hs : (∑ D ∈ children G B C, D.card) < C.card := by omega
  refine ⟨hs,?_⟩
  intro D hD
  exact lt_of_le_of_lt (Finset.single_le_sum (fun E _ => Nat.zero_le E.card) hD) hs

end StableMSR.Recovery.DecompositionSearch
open StableMSR.Recovery.DecompositionSearch StableMSR.Recovery.Havens
/-- A width-w decomposition supplies a progressing transition at every tight
rooted block. Every child again has a tight boundary of size at most w. -/
theorem solution {V : Type} [Fintype V] [DecidableEq V] {T : Type} [Fintype T] [DecidableEq T]
    {G : SimpleGraph V} {tree : SimpleGraph T} {bags : T → Finset V}
    (htd : RobertsonSeymour1986.GM5.IsTreeDecomposition G tree bags)
    (S C : Finset V) (w : ℕ) (hC : IsFlap G S C)
    (htight : boundary G C = S) (hroot : ∃ r, S ⊆ bags r)
    (hwidth : ∀ t, (bags t).card ≤ w+1) :
    ∃ B : Finset V,
      S ⊆ B ∧ B ⊆ S ∪ C ∧ B.card ≤ w+1 ∧ (B ∩ C).Nonempty ∧ S.card ≤ w ∧
      (∃ t, B ⊆ bags t) ∧
      (B ∩ C).card + (∑ D ∈ children G B C, D.card) = C.card ∧
      ∀ D ∈ children G B C,
        IsFlap G (boundary G D) D ∧ boundary G D ⊆ B ∧
        (boundary G D).card ≤ w ∧ D.card < C.card ∧
        ∃ r, boundary G D ⊆ bags r := by
  classical
  have htouch : ∀ s ∈ S, ∃ c ∈ C, G.Adj s c := by
    intro s hs
    rw [←htight] at hs
    obtain ⟨_,c,hc,hcs⟩ := mem_boundary.mp hs
    exact ⟨c,hc,hcs.symm⟩
  obtain ⟨t,hS,⟨c,hc,hct⟩,hScard,_⟩ :=
    boundary_advancing_bag_bound htd S C w hC.connected hC.avoids hroot htouch hwidth
  let B := bags t ∩ (S ∪ C)
  have hSB : S ⊆ B := fun s hs =>
    Finset.mem_inter.mpr ⟨hS hs,Finset.mem_union_left _ hs⟩
  have hBt : B ⊆ bags t := Finset.inter_subset_left
  have hp : (B ∩ C).Nonempty := ⟨c,Finset.mem_inter.mpr
    ⟨Finset.mem_inter.mpr ⟨hct,Finset.mem_union_right _ hc⟩,hc⟩⟩
  refine ⟨B,hSB,Finset.inter_subset_right,
    (Finset.card_le_card hBt).trans (hwidth t),hp,hScard,⟨t,hBt⟩,
    children_card_accounting hC hSB,?_⟩
  intro D hD
  have hf := (mem_children.mp hD).1
  have hDB : boundary G D ⊆ B := boundary_subset hf
  have hDr : ∃ r, boundary G D ⊆ bags r := ⟨t,fun v hv => hBt (hDB hv)⟩
  have hDt : ∀ s ∈ boundary G D, ∃ c ∈ D, G.Adj s c := by
    intro s hs
    obtain ⟨_,c,hc,hcs⟩ := mem_boundary.mp hs
    exact ⟨c,hc,hcs.symm⟩
  obtain ⟨_,_,_,hDw,_⟩ := boundary_advancing_bag_bound htd (boundary G D) D w
    hf.connected (boundary_disjoint G D) hDr hDt hwidth
  exact ⟨flap_at_boundary hf,hDB,hDw,(children_strictly_smaller hC hSB hp).2 D hD,hDr⟩

