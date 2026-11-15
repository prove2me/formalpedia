-- Prove2me | solution 1 for StableMSR.Recovery.DecompositionSearch.finite_decomposition_search
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-14T17:31:54.068503+00:00
-- url     : https://prove2.me/submissions/9e4fb6e2-ab07-4671-8247-4581339761fa

import Definitions.Def_StableMSR_DecompositionSearch_Recurrence
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Theorems.Thm_StableMSR_Recovery_DecompositionSearch_tight_block_progress
import Mathlib.Combinatorics.SimpleGraph.Sum
set_option autoImplicit false
open scoped Classical BigOperators
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
namespace StableMSR.Recovery.TreeBridge
open SimpleGraph
variable {T U : Type} (treeL : SimpleGraph T) (treeR : SimpleGraph U)

/-- The disjoint union of two trees, joined by one edge between specified roots. -/
def bridge (r : T) (s : U) : SimpleGraph (T ⊕ U) :=
  treeL.sum treeR ⊔ SimpleGraph.edge (.inl r) (.inr s)

@[simp] lemma bridge_adj_inl (r : T) (s : U) (t t' : T) :
    (bridge treeL treeR r s).Adj (.inl t) (.inl t') ↔ treeL.Adj t t' := by
  simp [bridge,SimpleGraph.edge_adj]
@[simp] lemma bridge_adj_inr (r : T) (s : U) (u u' : U) :
    (bridge treeL treeR r s).Adj (.inr u) (.inr u') ↔ treeR.Adj u u' := by
  simp [bridge,SimpleGraph.edge_adj]
@[simp] lemma bridge_adj_cross (r : T) (s : U) (t : T) (u : U) :
    (bridge treeL treeR r s).Adj (.inl t) (.inr u) ↔ t = r ∧ u = s := by
  simp [bridge,SimpleGraph.edge_adj]
@[simp] lemma bridge_adj_cross' (r : T) (s : U) (t : T) (u : U) :
    (bridge treeL treeR r s).Adj (.inr u) (.inl t) ↔ t = r ∧ u = s := by
  rw [SimpleGraph.adj_comm,bridge_adj_cross]

/-- Joining two finite trees by a single new edge produces a tree. -/
theorem bridge_isTree [Fintype T] [Fintype U] (r : T) (s : U)
    (hL : treeL.IsTree) (hR : treeR.IsTree) :
    (bridge treeL treeR r s).IsTree := by
  classical
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hL.connected.sum_sup_edge hR.connected,?_⟩
  have hc : Fintype.card (treeL.sum treeR).edgeSet =
      Fintype.card treeL.edgeSet + Fintype.card treeR.edgeSet := by
    rw [Fintype.card_congr (SimpleGraph.edgeSetSumEquiv (G := treeL) (H := treeR)),Fintype.card_sum]
  have he := SimpleGraph.card_edgeFinset_sup_edge (G := treeL.sum treeR)
    (SimpleGraph.not_adj_sum_inl_inr r s) (by simp : (Sum.inl r : T ⊕ U) ≠ Sum.inr s)
  rw [bridge,Nat.card_eq_fintype_card,← SimpleGraph.edgeFinset_card,he,
    SimpleGraph.edgeFinset_card,hc,Nat.card_eq_fintype_card,Fintype.card_sum]
  have hl := hL.card_edgeFinset
  have hr := hR.card_edgeFinset
  rw [SimpleGraph.edgeFinset_card] at hl hr
  omega

variable {V : Type} [DecidableEq V]
def bridgeBags (bagsL : T → Finset V) (bagsR : U → Finset V) : T ⊕ U → Finset V :=
  Sum.elim bagsL bagsR

def leftHom (r : T) (s : U) : treeL →g bridge treeL treeR r s where
  toFun := Sum.inl
  map_rel' h := (bridge_adj_inl treeL treeR r s _ _).mpr h

def rightHom (r : T) (s : U) : treeR →g bridge treeL treeR r s where
  toFun := Sum.inr
  map_rel' h := (bridge_adj_inr treeL treeR r s _ _).mpr h

lemma exists_bag_walk {T : Type} (tree : SimpleGraph T) (bags : T → Finset V)
    (hconn : tree.Connected)
    (hRI : ∀ a b c (p : tree.Walk a c), p.IsPath → b ∈ p.support → bags a ∩ bags c ⊆ bags b)
    {a b : T} {v : V} (ha : v ∈ bags a) (hb : v ∈ bags b) :
    ∃ p : tree.Walk a b, ∀ t ∈ p.support, v ∈ bags t := by
  obtain ⟨p,hp⟩ := hconn.exists_isPath a b
  exact ⟨p,fun t ht => hRI a t b p hp ht (Finset.mem_inter.mpr ⟨ha,hb⟩)⟩

/-- Occurrence sets remain connected when every vertex shared across sides belongs to both roots. -/
lemma exists_bridge_bag_walk (r : T) (s : U)
    (bagsL : T → Finset V) (bagsR : U → Finset V)
    (hL : treeL.Connected) (hR : treeR.Connected)
    (hLRI : ∀ a b c (p : treeL.Walk a c), p.IsPath → b ∈ p.support → bagsL a ∩ bagsL c ⊆ bagsL b)
    (hRRI : ∀ a b c (p : treeR.Walk a c), p.IsPath → b ∈ p.support → bagsR a ∩ bagsR c ⊆ bagsR b)
    (hoverlap : ∀ v a b, v ∈ bagsL a → v ∈ bagsR b → v ∈ bagsL r ∧ v ∈ bagsR s)
    {a b : T ⊕ U} {v : V} (ha : v ∈ bridgeBags bagsL bagsR a)
    (hb : v ∈ bridgeBags bagsL bagsR b) :
    ∃ p : (bridge treeL treeR r s).Walk a b,
      ∀ t ∈ p.support, v ∈ bridgeBags bagsL bagsR t := by
  have hliftL : ∀ {a b : T} (p : treeL.Walk a b), (∀ t ∈ p.support, v ∈ bagsL t) →
      ∀ t ∈ (p.map (leftHom treeL treeR r s)).support, v ∈ bridgeBags bagsL bagsR t := by
    intro a b p hp t ht
    rw [SimpleGraph.Walk.support_map] at ht
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
    exact hp u hu
  have hliftR : ∀ {a b : U} (p : treeR.Walk a b), (∀ t ∈ p.support, v ∈ bagsR t) →
      ∀ t ∈ (p.map (rightHom treeL treeR r s)).support, v ∈ bridgeBags bagsL bagsR t := by
    intro a b p hp t ht
    rw [SimpleGraph.Walk.support_map] at ht
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
    exact hp u hu
  have hcross : ∀ a b, v ∈ bagsL a → v ∈ bagsR b →
      ∃ p : (bridge treeL treeR r s).Walk (.inl a) (.inr b),
        ∀ t ∈ p.support, v ∈ bridgeBags bagsL bagsR t := by
    intro a b ha hb
    obtain ⟨hr,hs⟩ := hoverlap v a b ha hb
    obtain ⟨p,hp⟩ := exists_bag_walk treeL bagsL hL hLRI ha hr
    obtain ⟨q,hq⟩ := exists_bag_walk treeR bagsR hR hRRI hs hb
    have he : (bridge treeL treeR r s).Adj (.inl r) (.inr s) := by simp
    refine ⟨(p.map (leftHom treeL treeR r s)).append (.cons he (q.map (rightHom treeL treeR r s))),?_⟩
    intro t ht
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp ht with ht | ht
    · exact hliftL p hp t ht
    · change t ∈ Sum.inl r :: (q.map (rightHom treeL treeR r s)).support at ht
      rw [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact hr
      · exact hliftR q hq t ht
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      obtain ⟨p,hp⟩ := exists_bag_walk treeL bagsL hL hLRI ha hb
      exact ⟨p.map (leftHom treeL treeR r s),hliftL p hp⟩
    | inr b => exact hcross a b ha hb
  | inr a =>
    cases b with
    | inl b =>
      obtain ⟨p,hp⟩ := hcross b a hb ha
      refine ⟨p.reverse,?_⟩
      intro t ht
      apply hp t
      simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using ht
    | inr b =>
      obtain ⟨p,hp⟩ := exists_bag_walk treeR bagsR hR hRRI ha hb
      exact ⟨p.map (rightHom treeL treeR r s),hliftR p hp⟩

/-- The running-intersection property of the bridge construction. -/
theorem bridge_running_intersection [Fintype T] [Fintype U] (r : T) (s : U)
    (bagsL : T → Finset V) (bagsR : U → Finset V)
    (hL : treeL.IsTree) (hR : treeR.IsTree)
    (hLRI : ∀ a b c (p : treeL.Walk a c), p.IsPath → b ∈ p.support → bagsL a ∩ bagsL c ⊆ bagsL b)
    (hRRI : ∀ a b c (p : treeR.Walk a c), p.IsPath → b ∈ p.support → bagsR a ∩ bagsR c ⊆ bagsR b)
    (hoverlap : ∀ v a b, v ∈ bagsL a → v ∈ bagsR b → v ∈ bagsL r ∧ v ∈ bagsR s) :
    ∀ a b c (p : (bridge treeL treeR r s).Walk a c), p.IsPath → b ∈ p.support →
      bridgeBags bagsL bagsR a ∩ bridgeBags bagsL bagsR c ⊆ bridgeBags bagsL bagsR b := by
  classical
  intro a b c p hp hb v hv
  obtain ⟨hvA,hvC⟩ := Finset.mem_inter.mp hv
  obtain ⟨q,hq⟩ := exists_bridge_bag_walk treeL treeR r s bagsL bagsR hL.connected hR.connected
    hLRI hRRI hoverlap hvA hvC
  have heq : (⟨p,hp⟩ : (bridge treeL treeR r s).Path a c) = q.toPath :=
    (bridge_isTree treeL treeR r s hL hR).isAcyclic.subsingleton_path a c |>.elim _ _
  have hw : p = q.toPath.val := congrArg Subtype.val heq
  apply hq b
  exact SimpleGraph.Walk.support_toPath_subset_support q (hw ▸ hb)

end StableMSR.Recovery.TreeBridge
set_option autoImplicit false
open scoped Classical
namespace StableMSR.Recovery.DecompositionSearch
open RobertsonSeymour1986.GM5 Havens PartialDecompositions
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Any supplied width-w decomposition certifies acceptance of every tight
rooted block within depth equal to its number of interior vertices. -/
theorem accepts_of_decomposition {T : Type} [Fintype T] [DecidableEq T]
    {G : SimpleGraph V} {tree : SimpleGraph T} {bags : T → Finset V}
    (htd : IsTreeDecomposition G tree bags) (w : ℕ)
    (hwidth : ∀ t, (bags t).card ≤ w+1) (m : ℕ) :
    ∀ (S C : Finset V), IsFlap G S C → boundary G C = S →
      (∃ r, S ⊆ bags r) → C.card ≤ m → accepts G w m S C := by
  induction m with
  | zero =>
    intro S C hC htight hroot hsize
    have hp := hC.connected.1.card_pos
    omega
  | succ m ih =>
    intro S C hC htight hroot hsize
    obtain ⟨B,hSB,hBC,hBw,hp,_,_,_,hchildren⟩ :=
      tight_block_progress htd S C w hC htight hroot hwidth
    refine ⟨B,hSB,hBC,hBw,hp,?_⟩
    intro D hD
    obtain ⟨hf,_,hw,hsmall,hr⟩ := hchildren D hD
    exact ⟨hw,ih (boundary G D) D hf rfl hr (by omega)⟩

/-- The search never loses a successful state when its depth budget increases. -/
theorem accepts_mono {G : SimpleGraph V} {w m : ℕ} {S C : Finset V}
    (h : accepts G w m S C) : ∀ n, m ≤ n → accepts G w n S C := by
  induction m generalizing S C with
  | zero => exact False.elim h
  | succ m ih =>
    intro n hmn
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨B,hSB,hBC,hBw,hp,hchildren⟩ := h
      refine ⟨B,hSB,hBC,hBw,hp,?_⟩
      intro D hD
      exact ⟨(hchildren D hD).1,ih (hchildren D hD).2 n (by omega)⟩

/-- Strict child-size descent removes any need for an unbounded search budget:
an accepted valid component is already accepted within its own cardinality. -/
theorem accepts_normalize {G : SimpleGraph V} {w m : ℕ} {S C : Finset V}
    (hC : IsFlap G S C) (h : accepts G w m S C) :
    accepts G w C.card S C := by
  induction m generalizing S C with
  | zero => exact False.elim h
  | succ m ih =>
    obtain ⟨B,hSB,hBC,hBw,hp,hchildren⟩ := h
    have hcpos := hC.connected.1.card_pos
    obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcpos)
    rw [hn]
    refine ⟨B,hSB,hBC,hBw,hp,?_⟩
    intro D hD
    have hf : IsFlap G (boundary G D) D := flap_at_boundary (mem_children.mp hD).1
    have hnormalized := ih hf (hchildren D hD).2
    have hsmall := (children_strictly_smaller hC hSB hp).2 D hD
    exact ⟨(hchildren D hD).1,accepts_mono hnormalized n (by omega)⟩

/-- Finite global recognition tests precisely the initial connected components,
each with empty external boundary, at depth at most the input vertex count. -/
theorem recognizes_of_treewidthLE (G : SimpleGraph V) (w : ℕ)
    (h : TreewidthLE G w) : recognizes G w := by
  classical
  obtain ⟨T,ft,tree,bags,htd,hwidth⟩ := h
  letI : Fintype T := ft
  intro C hC
  have hf := mem_components.mp hC
  have hb : boundary G C = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
    (fun v hv => Finset.notMem_empty v (boundary_subset hf hv))
  obtain ⟨r⟩ := htd.1.connected.nonempty
  exact accepts_of_decomposition htd w hwidth (Fintype.card V) ∅ C hf hb
    ⟨r,Finset.empty_subset _⟩ (Finset.card_le_univ _)

end StableMSR.Recovery.DecompositionSearch
open scoped BigOperators
namespace StableMSR.Recovery.DecompositionSearch

/-- A finite rooted tree of bags, separated from graph coverage assertions. -/
structure RootedSystem (V : Type) [DecidableEq V] where
  Node : Type
  nodeFinite : Fintype Node
  nodeDecidable : DecidableEq Node
  tree : SimpleGraph Node
  bags : Node → Finset V
  root : Node
  isTree : tree.IsTree
  running : ∀ a b c (p : tree.Walk a c), p.IsPath → b ∈ p.support →
    bags a ∩ bags c ⊆ bags b

attribute [instance] RootedSystem.nodeFinite RootedSystem.nodeDecidable

variable {V : Type} [DecidableEq V]

def RootedSystem.singleton (B : Finset V) : RootedSystem V where
  Node := Unit
  nodeFinite := inferInstance
  nodeDecidable := inferInstance
  tree := ⊥
  bags := fun _ => B
  root := ()
  isTree := SimpleGraph.IsTree.of_subsingleton
  running := fun _ _ _ _ _ _ => Finset.inter_subset_left

def RootedSystem.join (L R : RootedSystem V)
    (hoverlap : ∀ v a b, v ∈ L.bags a → v ∈ R.bags b →
      v ∈ L.bags L.root ∧ v ∈ R.bags R.root) : RootedSystem V where
  Node := L.Node ⊕ R.Node
  nodeFinite := inferInstance
  nodeDecidable := inferInstance
  tree := TreeBridge.bridge L.tree R.tree L.root R.root
  bags := TreeBridge.bridgeBags L.bags R.bags
  root := .inl L.root
  isTree := TreeBridge.bridge_isTree L.tree R.tree L.root R.root L.isTree R.isTree
  running := TreeBridge.bridge_running_intersection L.tree R.tree L.root R.root
    L.bags R.bags L.isTree R.isTree L.running R.running hoverlap

/-- Glue any finite list of child trees to one new root bag. The exact bag
range and node count are preserved, with just one added root node. -/
theorem glue_list (B : Finset V) (ps : List (RootedSystem V))
    (hparent : ∀ P ∈ ps, ∀ t, P.bags t ∩ B ⊆ P.bags P.root)
    (hpair : ps.Pairwise (fun P Q => ∀ t u, P.bags t ∩ Q.bags u ⊆ B)) :
    ∃ R : RootedSystem V,
      R.bags R.root = B ∧
      (∀ A : Finset V, (∃ r, R.bags r = A) ↔
        A = B ∨ ∃ P ∈ ps, ∃ t, P.bags t = A) ∧
      Fintype.card R.Node = 1 + (ps.map (fun P => Fintype.card P.Node)).sum := by
  induction ps with
  | nil =>
    refine ⟨RootedSystem.singleton B,rfl,?_,?_⟩
    · intro A
      simp only [RootedSystem.singleton,List.not_mem_nil,false_and,exists_false,or_false]
      exact ⟨fun ⟨_,h⟩ => h.symm,fun h => ⟨(),h.symm⟩⟩
    · change Fintype.card Unit = 1 + (List.map (fun P : RootedSystem V => Fintype.card P.Node) []).sum
      simp only [List.map_nil,List.sum_nil,Nat.add_zero]
      exact Fintype.card_unit
  | cons P ps ih =>
    obtain ⟨hp,hps⟩ := List.pairwise_cons.mp hpair
    obtain ⟨R,hroot,hrange,hcard⟩ := ih (fun Q hQ => hparent Q (by simp [hQ])) hps
    have hoverlap : ∀ v a b, v ∈ R.bags a → v ∈ P.bags b →
        v ∈ R.bags R.root ∧ v ∈ P.bags P.root := by
      intro v a b hvR hvP
      have hvB : v ∈ B := by
        rcases (hrange (R.bags a)).mp ⟨a,rfl⟩ with he | ⟨Q,hQ,q,hq⟩
        · exact he ▸ hvR
        · exact hp Q hQ b q (Finset.mem_inter.mpr ⟨hvP,hq ▸ hvR⟩)
      exact ⟨hroot.symm ▸ hvB,hparent P (by simp) b (Finset.mem_inter.mpr ⟨hvP,hvB⟩)⟩
    refine ⟨R.join P hoverlap,hroot,?_,?_⟩
    · intro A
      constructor
      · rintro ⟨r,hr⟩
        cases r with
        | inl r =>
          rcases (hrange A).mp ⟨r,hr⟩ with h | ⟨Q,hQ,q,hq⟩
          · exact Or.inl h
          · exact Or.inr ⟨Q,by simp [hQ],q,hq⟩
        | inr r => exact Or.inr ⟨P,by simp,r,hr⟩
      · rintro (h | ⟨Q,hQ,q,hq⟩)
        · exact ⟨.inl R.root,hroot.trans h.symm⟩
        · rcases List.mem_cons.mp hQ with hQP | hQ
          · subst Q; exact ⟨.inr q,hq⟩
          · obtain ⟨r,hr⟩ := (hrange A).mpr (Or.inr ⟨Q,hQ,q,hq⟩)
            exact ⟨.inl r,hr⟩
    · change Fintype.card (R.Node ⊕ P.Node) = _
      rw [Fintype.card_sum,hcard]
      simp only [List.map_cons,List.sum_cons]
      omega

/-- A single new root joins a finite indexed family, with exactly the old bags
and the new root bag, and exactly one additional tree node. -/
theorem finite_glue {I : Type} [Fintype I] (B : Finset V) (child : I → RootedSystem V)
    (hparent : ∀ i t, (child i).bags t ∩ B ⊆ (child i).bags (child i).root)
    (hpair : ∀ i j, i ≠ j → ∀ t u, (child i).bags t ∩ (child j).bags u ⊆ B) :
    ∃ R : RootedSystem V,
      R.bags R.root = B ∧
      (∀ A : Finset V, (∃ r, R.bags r = A) ↔
        A = B ∨ ∃ i t, (child i).bags t = A) ∧
      Fintype.card R.Node = 1 + ∑ i, Fintype.card (child i).Node := by
  classical
  let ps := Finset.univ.toList.map child
  have hp : ∀ P ∈ ps, ∀ t, P.bags t ∩ B ⊆ P.bags P.root := by
    intro P hP
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hP
    exact hparent i
  have hq : ps.Pairwise (fun P Q => ∀ t u, P.bags t ∩ Q.bags u ⊆ B) := by
    apply List.pairwise_map.mpr
    apply (List.nodup_iff_pairwise_ne.mp (Finset.nodup_toList (Finset.univ : Finset I))).imp
    intro i j hne
    exact hpair i j hne
  obtain ⟨R,hr,ha,hn⟩ := glue_list B ps hp hq
  refine ⟨R,hr,?_,?_⟩
  · intro A
    rw [ha]
    simp [ps]
  · rw [hn]
    congr 1
    dsimp [ps]
    rw [List.map_map]
    simpa [Function.comp_def] using
      (List.sum_toFinset (fun i => Fintype.card (child i).Node)
        (Finset.nodup_toList (Finset.univ : Finset I))).symm

end StableMSR.Recovery.DecompositionSearch

open scoped BigOperators Classical
namespace StableMSR.Recovery.DecompositionSearch
open Havens PartialDecompositions
variable {V : Type} [Fintype V] [DecidableEq V]

theorem components_pairwise_disjoint (G : SimpleGraph V) (S : Finset V) :
    (PartialDecompositions.components G S : Set (Finset V)).PairwiseDisjoint id := by
  intro C hC D hD hne
  apply Finset.disjoint_left.mpr
  intro v hvC hvD
  exact hne (components_eq_of_mem hC hD hvC hvD)

theorem components_partition (G : SimpleGraph V) (S : Finset V) :
    (PartialDecompositions.components G S).biUnion id = Finset.univ \ S := by
  classical
  ext v
  simp only [Finset.mem_biUnion,id_eq,Finset.mem_sdiff,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨C,hC,hvC⟩ hvS
    exact Finset.disjoint_left.mp (mem_components.mp hC).avoids hvS hvC
  · intro hvS
    exact component_exists G S hvS

theorem components_card_sum (G : SimpleGraph V) (S : Finset V) :
    (∑ C ∈ PartialDecompositions.components G S, C.card) = Fintype.card V - S.card := by
  classical
  calc
    _ = ((PartialDecompositions.components G S).biUnion id).card := by
      simpa only [id_eq] using (Finset.card_biUnion (components_pairwise_disjoint G S)).symm
    _ = _ := by
      rw [components_partition,Finset.card_sdiff]
      simp

theorem components_subtype_card_sum (G : SimpleGraph V) (S : Finset V) :
    (∑ C : ↥(PartialDecompositions.components G S), C.val.card) = Fintype.card V - S.card := by
  classical
  rw [Finset.sum_coe_sort]
  exact components_card_sum G S

theorem components_empty_card_sum (G : SimpleGraph V) :
    (∑ C : ↥(PartialDecompositions.components G ∅), C.val.card) = Fintype.card V := by
  simpa using components_subtype_card_sum G ∅

end StableMSR.Recovery.DecompositionSearch

set_option autoImplicit false
open scoped Classical BigOperators
namespace StableMSR.Recovery.DecompositionSearch
open RobertsonSeymour1986.GM5 Havens PartialDecompositions
variable {V : Type} [Fintype V] [DecidableEq V]

/-- An ambient representation of a decomposition of the indicated induced block. -/
structure BlockSystem (G : SimpleGraph V) (w : ℕ) (S C : Finset V)
    (R : RootedSystem V) : Prop where
  contained : ∀ t, R.bags t ⊆ S ∪ C
  vertex : ∀ v ∈ S ∪ C, ∃ t, v ∈ R.bags t
  edge : ∀ x ∈ S ∪ C, ∀ y ∈ S ∪ C, G.Adj x y → ∃ t, x ∈ R.bags t ∧ y ∈ R.bags t
  boundary : S ⊆ R.bags R.root
  width : ∀ t, (R.bags t).card ≤ w+1

/-- Restrict the ambient bags to their region to obtain the canonical induced
graph decomposition. Ambient containment ensures no information is removed. -/
theorem BlockSystem.induced {G : SimpleGraph V} {w : ℕ} {S C : Finset V}
    {R : RootedSystem V} (h : BlockSystem G w S C R) :
    IsTreeDecomposition (G.induce ((S ∪ C : Finset V) : Set V)) R.tree
      (fun t => (R.bags t).subtype (· ∈ S ∪ C)) := by
  classical
  refine ⟨R.isTree,?_,?_,?_⟩
  · intro v
    obtain ⟨t,ht⟩ := h.vertex v.val v.property
    exact ⟨t,Finset.mem_subtype.mpr ht⟩
  · intro x y hxy
    obtain ⟨t,hx,hy⟩ := h.edge x.val x.property y.val y.property hxy
    exact ⟨t,Finset.mem_subtype.mpr hx,Finset.mem_subtype.mpr hy⟩
  · intro a b c p hp hb v hv
    obtain ⟨ha,hc⟩ := Finset.mem_inter.mp hv
    exact Finset.mem_subtype.mpr (R.running a b c p hp hb
      (Finset.mem_inter.mpr ⟨Finset.mem_subtype.mp ha,Finset.mem_subtype.mp hc⟩))

/-- Every successful finite search reconstructs a genuine rooted decomposition
with at most one bag per interior vertex. -/
theorem accepts_sound {G : SimpleGraph V} {w m : ℕ} {S C : Finset V}
    (ha : accepts G w m S C) (hC : IsFlap G S C) :
    ∃ R : RootedSystem V, BlockSystem G w S C R ∧ Fintype.card R.Node ≤ C.card := by
  classical
  induction m generalizing S C with
  | zero => exact False.elim ha
  | succ m ih =>
    obtain ⟨B,hSB,hBC,hBw,hprogress,haccept⟩ := ha
    let I := ↥(children G B C)
    have hex : ∀ D : I, ∃ R : RootedSystem V,
        BlockSystem G w (boundary G D.val) D.val R ∧ Fintype.card R.Node ≤ D.val.card := by
      intro D
      exact ih (haccept D.val D.property).2
        (flap_at_boundary (mem_children.mp D.property).1)
    choose child hchild using hex
    have hparent : ∀ (D : I) t, (child D).bags t ∩ B ⊆ (child D).bags (child D).root := by
      intro D t v hv
      obtain ⟨hvt,hvB⟩ := Finset.mem_inter.mp hv
      rcases Finset.mem_union.mp ((hchild D).1.contained t hvt) with hvb | hvD
      · exact (hchild D).1.boundary hvb
      · exact False.elim (Finset.disjoint_left.mp (mem_children.mp D.property).1.avoids hvB hvD)
    have hcross : ∀ (D E : I), D ≠ E → ∀ t u,
        (child D).bags t ∩ (child E).bags u ⊆ B := by
      intro D E hne t u v hv
      obtain ⟨hD,hE⟩ := Finset.mem_inter.mp hv
      rcases Finset.mem_union.mp ((hchild D).1.contained t hD) with hbD | hvD
      · exact boundary_subset (mem_children.mp D.property).1 hbD
      rcases Finset.mem_union.mp ((hchild E).1.contained u hE) with hbE | hvE
      · exact boundary_subset (mem_children.mp E.property).1 hbE
      · exact False.elim (Finset.disjoint_left.mp
          (children_disjoint D.property E.property (fun h => hne (Subtype.ext h))) hvD hvE)
    obtain ⟨R,hroot,hocc,hsize⟩ := finite_glue B child hparent hcross
    have hrootmem {v : V} (hv : v ∈ B) : v ∈ R.bags R.root := hroot.symm ▸ hv
    have htransfer (D : I) (t : (child D).Node) : ∃ r, R.bags r = (child D).bags t :=
      (hocc ((child D).bags t)).mpr (.inr ⟨D,t,rfl⟩)
    have hlocate {v : V} (hvC : v ∈ C) (hvB : v ∉ B) :
        ∃ D : I, v ∈ D.val := by
      have hv : v ∈ (children G B C).biUnion id := by
        rw [children_partition hC hSB]
        exact Finset.mem_sdiff.mpr ⟨hvC,hvB⟩
      obtain ⟨D,hD,hvD⟩ := Finset.mem_biUnion.mp hv
      exact ⟨⟨D,hD⟩,hvD⟩
    refine ⟨R,⟨?_,?_,?_,?_,?_⟩,?_⟩
    · intro t v hv
      rcases (hocc (R.bags t)).mp ⟨t,rfl⟩ with ht | ⟨D,u,hu⟩
      · exact hBC (ht ▸ hv)
      · rw [←hu] at hv
        rcases Finset.mem_union.mp ((hchild D).1.contained u hv) with hb | hd
        · exact hBC (boundary_subset (mem_children.mp D.property).1 hb)
        · exact Finset.mem_union_right _ ((mem_children.mp D.property).2 hd)
    · intro v hv
      by_cases hvB : v ∈ B
      · exact ⟨R.root,hrootmem hvB⟩
      have hvC : v ∈ C := (Finset.mem_union.mp hv).resolve_left (fun hs => hvB (hSB hs))
      obtain ⟨D,hvD⟩ := hlocate hvC hvB
      obtain ⟨t,ht⟩ := (hchild D).1.vertex v (Finset.mem_union_right _ hvD)
      obtain ⟨r,hr⟩ := htransfer D t
      exact ⟨r,hr.symm ▸ ht⟩
    · have hout : ∀ x ∈ S ∪ C, ∀ y ∈ S ∪ C, G.Adj x y → x ∉ B →
          ∃ r, x ∈ R.bags r ∧ y ∈ R.bags r := by
        intro x hx y hy hxy hxB
        have hxC : x ∈ C := (Finset.mem_union.mp hx).resolve_left (fun hs => hxB (hSB hs))
        obtain ⟨D,hxD⟩ := hlocate hxC hxB
        have hyregion : y ∈ boundary G D.val ∪ D.val := by
          by_cases hyD : y ∈ D.val
          · exact Finset.mem_union_right _ hyD
          · exact Finset.mem_union_left _ (mem_boundary.mpr ⟨hyD,x,hxD,hxy⟩)
        obtain ⟨t,hxt,hyt⟩ := (hchild D).1.edge x (Finset.mem_union_right _ hxD) y hyregion hxy
        obtain ⟨r,hr⟩ := htransfer D t
        exact ⟨r,hr.symm ▸ hxt,hr.symm ▸ hyt⟩
      intro x hx y hy hxy
      by_cases hxB : x ∈ B
      · by_cases hyB : y ∈ B
        · exact ⟨R.root,hrootmem hxB,hrootmem hyB⟩
        · obtain ⟨r,hy',hx'⟩ := hout y hy x hx hxy.symm hyB
          exact ⟨r,hx',hy'⟩
      · exact hout x hx y hy hxy hxB
    · exact fun v hv => hrootmem (hSB hv)
    · intro t
      rcases (hocc (R.bags t)).mp ⟨t,rfl⟩ with ht | ⟨D,u,hu⟩
      · simpa only [ht] using hBw
      · simpa only [←hu] using (hchild D).1.width u
    · have hsum : (∑ D : I, Fintype.card (child D).Node) ≤ ∑ D : I, D.val.card :=
        Finset.sum_le_sum (fun D _ => (hchild D).2)
      have hsmall : (∑ D : I, D.val.card) < C.card := by
        change (∑ D : ↥(children G B C), D.val.card) < C.card
        rw [Finset.sum_coe_sort]
        exact (children_strictly_smaller hC hSB hprogress).1
      rw [hsize]
      omega

end StableMSR.Recovery.DecompositionSearch
open scoped Classical BigOperators
namespace StableMSR.Recovery.DecompositionSearch
open RobertsonSeymour1986.GM5 Havens PartialDecompositions
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Join the initial connected-component certificates to an empty root. -/
theorem recognizes_system (G : SimpleGraph V) (w : ℕ) (h : recognizes G w) :
    ∃ R : RootedSystem V, IsTreeDecomposition G R.tree R.bags ∧
      (∀ t, (R.bags t).card ≤ w+1) ∧ Fintype.card R.Node ≤ Fintype.card V + 1 := by
  classical
  let I := ↥(PartialDecompositions.components G ∅)
  have hex : ∀ C : I, ∃ R : RootedSystem V,
      BlockSystem G w ∅ C.val R ∧ Fintype.card R.Node ≤ C.val.card := by
    intro C
    exact accepts_sound (h C.val C.property) (mem_components.mp C.property)
  choose child hchild using hex
  have hparent : ∀ (C : I) t, (child C).bags t ∩ ∅ ⊆ (child C).bags (child C).root := by
    intro C t; simp
  have hcontained (C : I) (t : (child C).Node) : (child C).bags t ⊆ C.val := by
    simpa only [Finset.empty_union] using (hchild C).1.contained t
  have hpair : ∀ (C D : I), C ≠ D → ∀ t u,
      (child C).bags t ∩ (child D).bags u ⊆ ∅ := by
    intro C D hne t u v hv
    obtain ⟨hvC,hvD⟩ := Finset.mem_inter.mp hv
    exact False.elim (Finset.disjoint_left.mp
      (components_pairwise_disjoint G ∅ C.property D.property
        (fun he => hne (Subtype.ext he))) (hcontained C t hvC) (hcontained D u hvD))
  obtain ⟨R,hr,hbags,hsize⟩ := finite_glue (∅ : Finset V) child hparent hpair
  have liftbag (C : I) (t : (child C).Node) : ∃ r, R.bags r = (child C).bags t :=
    (hbags _).mpr (.inr ⟨C,t,rfl⟩)
  refine ⟨R,⟨R.isTree,?_,?_,R.running⟩,?_,?_⟩
  · intro v
    obtain ⟨C,hC,hvC⟩ := component_exists G ∅ (by simp : v ∉ (∅ : Finset V))
    obtain ⟨t,ht⟩ := (hchild ⟨C,hC⟩).1.vertex v (by simpa using hvC)
    obtain ⟨r,hr⟩ := liftbag ⟨C,hC⟩ t
    exact ⟨r,hr.symm ▸ ht⟩
  · intro x y hxy
    obtain ⟨C,hC,hxC⟩ := component_exists G ∅ (by simp : x ∉ (∅ : Finset V))
    have hyC := (mem_components.mp hC).closed x hxC y hxy (by simp)
    obtain ⟨t,hxt,hyt⟩ := (hchild ⟨C,hC⟩).1.edge x (by simpa using hxC)
      y (by simpa using hyC) hxy
    obtain ⟨r,hr⟩ := liftbag ⟨C,hC⟩ t
    exact ⟨r,hr.symm ▸ hxt,hr.symm ▸ hyt⟩
  · intro t
    rcases (hbags (R.bags t)).mp ⟨t,rfl⟩ with he | ⟨C,u,hu⟩
    · simp [he]
    · rw [←hu]; exact (hchild C).1.width u
  · rw [hsize]
    have hs : (∑ C : I, Fintype.card (child C).Node) ≤ ∑ C : I, C.val.card :=
      Finset.sum_le_sum (fun C _ => (hchild C).2)
    have hc := components_empty_card_sum G
    change (∑ C : I, C.val.card) = Fintype.card V at hc
    omega

/-- Successful finite search returns an actual width-w decomposition with at
most n+1 bags, including the empty-graph case. -/
theorem recognizes_small_decomposition (G : SimpleGraph V) (w : ℕ)
    (h : recognizes G w) :
    ∃ (T : Type) (ft : Fintype T) (tree : SimpleGraph T) (bags : T → Finset V),
      IsTreeDecomposition G tree bags ∧ (∀ t, (bags t).card ≤ w+1) ∧
      @Fintype.card T ft ≤ Fintype.card V + 1 := by
  obtain ⟨R,htd,hw,hn⟩ := recognizes_system G w h
  exact ⟨R.Node,R.nodeFinite,R.tree,R.bags,htd,hw,hn⟩

end StableMSR.Recovery.DecompositionSearch
open StableMSR.Recovery.DecompositionSearch RobertsonSeymour1986.GM5
/-- Exact recognition and a controlled-size canonical output certificate. -/
theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (w : ℕ) :
    (recognizes G w ↔ TreewidthLE G w) ∧
    (recognizes G w →
      ∃ (T : Type) (ft : Fintype T) (tree : SimpleGraph T) (bags : T → Finset V),
        IsTreeDecomposition G tree bags ∧ (∀ t, (bags t).card ≤ w+1) ∧
        @Fintype.card T ft ≤ Fintype.card V + 1) := by
  refine ⟨⟨?_,recognizes_of_treewidthLE G w⟩,recognizes_small_decomposition G w⟩
  intro h
  obtain ⟨T,ft,tree,bags,htd,hw,_⟩ := recognizes_small_decomposition G w h
  exact ⟨T,ft,tree,bags,htd,hw⟩

