-- Prove2me | solution 1 for StableMSR.Recovery.TreeDP.binary_plan_from_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-14T09:08:36.227377+00:00
-- url     : https://prove2.me/submissions/d06ea778-fa16-4f09-b8dd-2340fc05ddb2

import Definitions.Def_Mazoit2013_PartialDecompositions
import Definitions.Def_StableMSR_BinaryTreeDP_Plan
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Tauto
open RobertsonSeymour1986.GM5 StableMSR.Recovery.Havens
namespace StarAux
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
end StarAux
open StarAux
namespace StableMSR.Recovery.PartialDecompositions
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
namespace StableMSR.Recovery.Havens
variable {V : Type} [DecidableEq V]
lemma ConnectedSet.induce_connected {G : SimpleGraph V} {C : Finset V}
    (hC : ConnectedSet G C) : (G.induce (C : Set V)).Connected := by
  refine { preconnected := ?_, nonempty := ?_ }
  · intro x y
    obtain ⟨p, hp⟩ := hC.2 x.val x.property y.val y.property
    exact ⟨p.induce (C : Set V) hp⟩
  · obtain ⟨x, hx⟩ := hC.1
    exact ⟨⟨x, hx⟩⟩

end StableMSR.Recovery.Havens
namespace StableMSR.Recovery.TreeDP
/-- A duplicate bag enforces no extra constraint and contributes neither count nor cost. -/
def BagData.neutral {V X : Type*} (d : BagData V X) : BagData V X :=
  ⟨d.bag,d.choices,fun _ => True,fun _ => 0,fun _ => 0⟩
/-- Explicit binary conversion of a finite family of child plans. The original parent
record occurs once, at the final leaf; the extra join records are neutral copies. -/
def joinForest {V X : Type*} (d : BagData V X) : List (Plan V X) → Plan V X
  | [] => .leaf d
  | p :: ps => .branch d.neutral p (joinForest d ps)
@[simp] theorem joinForest_root_bag {V X : Type*} (d : BagData V X) (ps : List (Plan V X)) :
    (joinForest d ps).root.bag = d.bag := by cases ps <;> rfl
@[simp] theorem joinForest_root_choices {V X : Type*} (d : BagData V X) (ps : List (Plan V X)) :
    (joinForest d ps).root.choices = d.choices := by cases ps <;> rfl
/-- Binary conversion preserves exactly the union of the parent and child scopes. -/
theorem mem_joinForest_scope {V X : Type*} [DecidableEq V]
    (d : BagData V X) (ps : List (Plan V X)) (v : V) :
    v ∈ (joinForest d ps).scope ↔ v ∈ d.bag ∨ ∃ p ∈ ps, v ∈ p.scope := by
  induction ps with
  | nil => simp [joinForest,Plan.scope]
  | cons p ps ih =>
    simp only [joinForest,Plan.scope,BagData.neutral,Finset.mem_union,ih,List.mem_cons]
    constructor
    · rintro ((hd | hp) | hd | ⟨q,hq,hv⟩)
      · exact Or.inl hd
      · exact Or.inr ⟨p,Or.inl rfl,hp⟩
      · exact Or.inl hd
      · exact Or.inr ⟨q,Or.inr hq,hv⟩
    · rintro (hd | ⟨q,hq,hv⟩)
      · exact Or.inl (Or.inl hd)
      · rcases hq with rfl | hq
        · exact Or.inl (Or.inr hv)
        · exact Or.inr (Or.inr ⟨q,hq,hv⟩)
/-- Arbitrary fanout can be converted to a coherent binary plan without changing bags. -/
theorem joinForest_coherent {V X : Type*} [DecidableEq V]
    (d : BagData V X) (ps : List (Plan V X))
    (hc : ∀ p ∈ ps, p.Coherent)
    (hb : ∀ p ∈ ps, p.scope ∩ d.bag ⊆ p.root.bag)
    (hpair : ps.Pairwise (fun p q => p.scope ∩ q.scope ⊆ d.bag)) :
    (joinForest d ps).Coherent := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    obtain ⟨hp,hps⟩ := List.pairwise_cons.mp hpair
    refine ⟨hc p (by simp),ih (fun q hq => hc q (by simp [hq]))
      (fun q hq => hb q (by simp [hq])) hps,hb p (by simp),?_,?_⟩
    · rw [joinForest_root_bag]
      exact Finset.inter_subset_right
    · intro v hv
      obtain ⟨hvp,hvr⟩ := Finset.mem_inter.mp hv
      rcases (mem_joinForest_scope d ps v).mp hvr with hd | ⟨q,hq,hvq⟩
      · exact hd
      · exact hp q hq (Finset.mem_inter.mpr ⟨hvp,hvq⟩)
@[simp] theorem neutral_local {V X : Type*} (d : BagData V X) : d.neutral.Local := by
  intro a b hab
  exact ⟨Iff.rfl,rfl,rfl⟩
theorem joinForest_local {V X : Type*} (d : BagData V X) (ps : List (Plan V X))
    (hd : d.Local) (hp : ∀ p ∈ ps, p.Local) : (joinForest d ps).Local := by
  induction ps with
  | nil => exact hd
  | cons p ps ih =>
    exact ⟨neutral_local d,hp p (by simp),ih (fun q hq => hp q (by simp [hq]))⟩
/-- Neutral copies neither repeat nor remove any constraint. -/
theorem joinForest_valid_iff {V X : Type*} (d : BagData V X) (ps : List (Plan V X))
    (a : V → X) :
    (joinForest d ps).AllValid a ↔ d.valid a ∧ ∀ p ∈ ps, p.AllValid a := by
  induction ps with
  | nil => simp [joinForest,Plan.AllValid]
  | cons p ps ih =>
    simp only [joinForest,Plan.AllValid,BagData.neutral,ih,true_and,List.forall_mem_cons]
    constructor
    · rintro ⟨hp,hd,hps⟩; exact ⟨hd,hp,hps⟩
    · rintro ⟨hd,hp,hps⟩; exact ⟨hp,hd,hps⟩
/-- The original count contribution occurs once, regardless of fanout. -/
theorem joinForest_count {V X : Type*} (d : BagData V X) (ps : List (Plan V X))
    (a : V → X) : (joinForest d ps).totalCount a =
      d.count a + (ps.map (fun p => p.totalCount a)).sum := by
  induction ps with
  | nil => simp [joinForest,Plan.totalCount]
  | cons p ps ih => simp [joinForest,Plan.totalCount,BagData.neutral,ih,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
/-- The original objective contribution occurs once, regardless of fanout. -/
theorem joinForest_weight {V X : Type*} (d : BagData V X) (ps : List (Plan V X))
    (a : V → X) : (joinForest d ps).totalWeight a =
      d.weight a + (ps.map (fun p => p.totalWeight a)).sum := by
  induction ps with
  | nil => simp [joinForest,Plan.totalWeight]
  | cons p ps ih => simp [joinForest,Plan.totalWeight,BagData.neutral,ih,add_comm,add_left_comm,add_assoc]
/-- Exactly one extra binary join per original child, with no hidden combinatorial blowup. -/
theorem joinForest_nodes {V X : Type*} (d : BagData V X) (ps : List (Plan V X)) :
    (joinForest d ps).nodes = 1 + ps.length + (ps.map Plan.nodes).sum := by
  induction ps with
  | nil => simp [joinForest,Plan.nodes]
  | cons p ps ih => simp [joinForest,Plan.nodes,ih]; omega
/-- A predicate about every bag record; useful for preserving width and table bounds. -/
lemma joinForest_allData {V X : Type*} (d : BagData V X) (ps : List (Plan V X))
    (P : BagData V X → Prop) (hd : P d) (hn : P d.neutral)
    (hps : ∀ p ∈ ps, p.AllData P) : (joinForest d ps).AllData P := by
  induction ps with
  | nil => exact hd
  | cons p ps ih => exact ⟨hn,hps p (by simp),ih (fun q hq => hps q (by simp [hq]))⟩
theorem joinForest_bag_bounds {V X : Type*} (d : BagData V X) (ps : List (Plan V X))
    (width choices : ℕ) (hd : d.bag.card ≤ width ∧ d.choices.card ≤ choices)
    (hps : ∀ p ∈ ps, p.AllData (fun d => d.bag.card ≤ width ∧ d.choices.card ≤ choices)) :
    (joinForest d ps).AllData (fun d => d.bag.card ≤ width ∧ d.choices.card ≤ choices) :=
  joinForest_allData d ps _ hd hd hps
end StableMSR.Recovery.TreeDP
open RobertsonSeymour1986.GM5
namespace StableMSR.Recovery.TreeDP
open Havens PartialDecompositions
variable {V T : Type} [DecidableEq V] [DecidableEq T]
/-- An avoiding walk cannot leave a component after the root has been deleted. -/
lemma walk_stays_in_root_component {tree : SimpleGraph T} {root : T} {C : Finset T}
    (hC : IsFlap tree {root} C) {x y : T} (p : tree.Walk x y)
    (hx : x ∈ C) (hp : root ∉ p.support) : y ∈ C := by
  refine mem_of_walk_closed (C := C) (D := p.support.toFinset) ?_ p hx ?_
  · intro a ha b hab hb
    apply hC.closed a ha b hab
    intro hbr
    have he : b = root := Finset.mem_singleton.mp hbr
    exact hp (he ▸ List.mem_toFinset.mp hb)
  · intro z hz
    exact List.mem_toFinset.mpr hz
/-- Every root-to-component path starts with a neighbor belonging to that component. -/
lemma first_neighbor_in_component {tree : SimpleGraph T} {root s : T} {C : Finset T}
    (hC : IsFlap tree {root} C) (hs : s ∈ C)
    (p : tree.Walk root s) (hp : p.IsPath) :
    ∃ c ∈ C, tree.Adj root c ∧ c ∈ p.support := by
  cases p with
  | nil => exact False.elim (Finset.disjoint_left.mp hC.avoids (Finset.mem_singleton_self _) hs)
  | @cons r c s hrc p =>
    have hn : root ∉ p.support := (SimpleGraph.Walk.cons_isPath_iff hrc p).mp hp |>.2
    refine ⟨c,?_,hrc,by simp⟩
    apply walk_stays_in_root_component hC p.reverse hs
    simpa using hn
/-- In a tree each component after deleting the root has precisely one root neighbor. -/
theorem root_component_unique_neighbor {tree : SimpleGraph T} (htree : tree.IsTree)
    {root : T} {C : Finset T} (hC : IsFlap tree {root} C) :
    ∃ c ∈ C, tree.Adj root c ∧ ∀ d ∈ C, tree.Adj root d → d = c := by
  classical
  obtain ⟨s,hs⟩ := hC.connected.1
  obtain ⟨p,hp⟩ := htree.connected.exists_isPath root s
  obtain ⟨c,hc,hrc,_⟩ := first_neighbor_in_component hC hs p hp
  refine ⟨c,hc,hrc,?_⟩
  intro d hd hrd
  obtain ⟨q,hq⟩ := hC.connected.2 c hc d hd
  have hn : root ∉ q.toPath.val.support := by
    intro hr
    exact Finset.disjoint_left.mp hC.avoids (Finset.mem_singleton_self _) (hq _ (q.support_toPath_subset_support hr))
  have hpath : (SimpleGraph.Walk.cons hrc q.toPath.val).IsPath := q.toPath.property.cons hn
  have he : (⟨.cons hrc q.toPath.val,hpath⟩ : tree.Path root d) = SimpleGraph.Path.singleton hrd :=
    htree.isAcyclic.subsingleton_path root d |>.elim _ _
  have hcpath : c ∈ (SimpleGraph.Walk.cons hrc q.toPath.val).support := by simp
  have heWalk : SimpleGraph.Walk.cons hrc q.toPath.val = hrd.toWalk := congrArg Subtype.val he
  rw [heWalk] at hcpath
  have hc_or : c = root ∨ c = d := by simpa using hcpath
  exact (hc_or.resolve_left hrc.ne.symm).symm
/-- Every recursive child tree has strictly fewer vertices than the original tree. -/
theorem root_component_card_lt [Fintype T] {tree : SimpleGraph T} {root : T}
    {C : Finset T} (hC : IsFlap tree {root} C) : C.card < Fintype.card T := by
  have hn : root ∉ C := fun hr => Finset.disjoint_left.mp hC.avoids (Finset.mem_singleton_self _) hr
  simpa only [Finset.card_univ] using Finset.card_lt_univ_of_notMem hn
end StableMSR.Recovery.TreeDP
open scoped BigOperators
namespace StableMSR.Recovery.TreeDP.TreeConstruction
open Havens PartialDecompositions
variable {V X T : Type} [DecidableEq V] [DecidableEq T]
def RunningIntersection (tree : SimpleGraph T) (bags : T → Finset V) : Prop :=
  ∀ a b c (p : tree.Walk a c), p.IsPath → b ∈ p.support → bags a ∩ bags c ⊆ bags b
lemma component_disjoint [Fintype T] {tree : SimpleGraph T} {root : T}
    {C D : Finset T} (hC : C ∈ PartialDecompositions.components tree {root}) (hD : D ∈ PartialDecompositions.components tree {root})
    (hne : C ≠ D) : Disjoint C D := by
  apply Finset.disjoint_left.mpr
  intro v hvC hvD
  exact hne (components_eq_of_mem hC hD hvC hvD)
lemma components_union [Fintype T] (tree : SimpleGraph T) (root : T) :
    (PartialDecompositions.components tree {root}).biUnion id = Finset.univ.erase root := by
  classical
  ext t
  simp only [Finset.mem_biUnion, id_eq, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨C,hC,ht⟩ he
    subst t
    exact Finset.disjoint_left.mp (mem_components.mp hC).avoids (Finset.mem_singleton_self _) ht
  · intro ht
    exact component_exists tree {root} (by simpa using ht)
lemma sum_components [Fintype T] {M : Type*} [AddCommMonoid M]
    (tree : SimpleGraph T) (root : T) (f : T → M) :
    f root + ∑ C : ↥(PartialDecompositions.components tree {root}), ∑ t : ↥C.val, f t.val = ∑ t, f t := by
  classical
  have hs : (∑ C : ↥(PartialDecompositions.components tree {root}), ∑ t : ↥C.val, f t.val) =
      ∑ t ∈ Finset.univ.erase root, f t := by
    simp only [Finset.sum_coe_sort]
    rw [Finset.sum_coe_sort (PartialDecompositions.components tree {root}) (fun C => ∑ t ∈ C, f t)]
    rw [←Finset.sum_biUnion (fun C hC D hD hne => component_disjoint hC hD hne)]
    change (∑ t ∈ (PartialDecompositions.components tree {root}).biUnion id, f t) = _
    rw [components_union]
  rw [hs]
  exact Finset.add_sum_erase _ _ (Finset.mem_univ root)
lemma induced_running {tree : SimpleGraph T} {bags : T → Finset V}
    (hri : RunningIntersection tree bags) (C : Finset T) :
    RunningIntersection (tree.induce (C : Set T)) (fun t => bags t.val) := by
  intro a b c p hp hb
  let incl : tree.induce (C : Set T) →g tree := ⟨Subtype.val,fun h => h⟩
  apply hri a.val b.val c.val (p.map incl) (hp.map Subtype.val_injective)
  simpa only [SimpleGraph.Walk.support_map, List.mem_map] using ⟨b,hb,rfl⟩
lemma component_boundary {tree : SimpleGraph T} (ht : tree.IsTree) {bags : T → Finset V}
    (hri : RunningIntersection tree bags) {root c : T} {C : Finset T}
    (hC : IsFlap tree {root} C) (hc : c ∈ C) (hrc : tree.Adj root c) :
    C.biUnion bags ∩ bags root ⊆ bags c := by
  classical
  intro v hv
  obtain ⟨hvs,hvr⟩ := Finset.mem_inter.mp hv
  obtain ⟨s,hs,hvs⟩ := Finset.mem_biUnion.mp hvs
  obtain ⟨p,hp⟩ := ht.connected.exists_isPath root s
  obtain ⟨d,hd,hrd,hpd⟩ := first_neighbor_in_component hC hs p hp
  obtain ⟨chosen,_,_,huniq⟩ := root_component_unique_neighbor ht hC
  have hdc : d = c := (huniq d hd hrd).trans (huniq c hc hrc).symm
  subst d
  exact hri root c s p hp hpd (Finset.mem_inter.mpr ⟨hvr,hvs⟩)
lemma distinct_scopes {tree : SimpleGraph T} (ht : tree.IsTree) {bags : T → Finset V}
    (hri : RunningIntersection tree bags) {root : T} {C D : Finset T}
    (hC : IsFlap tree {root} C) (hD : IsFlap tree {root} D) (hne : C ≠ D) :
    (C.biUnion bags) ∩ (D.biUnion bags) ⊆ bags root := by
  classical
  intro v hv
  obtain ⟨hvC,hvD⟩ := Finset.mem_inter.mp hv
  obtain ⟨s,hs,hvs⟩ := Finset.mem_biUnion.mp hvC
  obtain ⟨t,ht',hvt⟩ := Finset.mem_biUnion.mp hvD
  obtain ⟨p,hp⟩ := ht.connected.exists_isPath s t
  have hroot : root ∈ p.support := by
    by_contra hn
    have htC := walk_stays_in_root_component hC p hs hn
    have hDC : D ⊆ C := flap_contains_touching hC hD.connected hD.avoids (.inl ⟨t,htC,ht'⟩)
    have hCD : C ⊆ D := flap_contains_touching hD hC.connected hC.avoids (.inl ⟨t,ht',htC⟩)
    exact hne (Finset.Subset.antisymm hCD hDC)
  exact hri s root t p hp hroot (Finset.mem_inter.mpr ⟨hvs,hvt⟩)
structure Realization [Fintype T] (data : T → BagData V X) (root : T)
    (width choices : ℕ) (p : Plan V X) : Prop where
  coherent : p.Coherent
  local_data : p.Local
  root_bag : p.root.bag = (data root).bag
  root_choices : p.root.choices = (data root).choices
  scope : ∀ v, v ∈ p.scope ↔ ∃ t, v ∈ (data t).bag
  valid : ∀ a, p.AllValid a ↔ ∀ t, (data t).valid a
  choice_cover : ∀ whole, p.AllData (fun d => ∃ a ∈ d.choices, AgreeOn d.bag whole a) ↔
    ∀ t, ∃ a ∈ (data t).choices, AgreeOn (data t).bag whole a
  count : ∀ a, p.totalCount a = ∑ t, (data t).count a
  weight : ∀ a, p.totalWeight a = ∑ t, (data t).weight a
  nodes : p.nodes + 1 = 2 * Fintype.card T
  bound : p.AllData (fun d => d.bag.card ≤ width ∧ d.choices.card ≤ choices)
lemma sum_univ_list {I M : Type*} [Fintype I] [AddCommMonoid M] (f : I → M) :
    (Finset.univ.toList.map f).sum = ∑ i, f i := by
  classical
  simpa using (List.sum_toFinset f (Finset.nodup_toList Finset.univ)).symm
lemma joinForest_choice_cover (d : BagData V X) (ps : List (Plan V X)) (whole : V → X) :
    (joinForest d ps).AllData (fun d => ∃ a ∈ d.choices, AgreeOn d.bag whole a) ↔
      (∃ a ∈ d.choices, AgreeOn d.bag whole a) ∧
      ∀ p ∈ ps, p.AllData (fun d => ∃ a ∈ d.choices, AgreeOn d.bag whole a) := by
  induction ps with
  | nil => simp [joinForest,Plan.AllData]
  | cons p ps ih =>
    simp only [joinForest,Plan.AllData,BagData.neutral,ih,List.forall_mem_cons]
    tauto
/-- Recursion on the number of tree vertices constructs the entire binary plan. -/
theorem realization_of_card (m : ℕ) :
    ∀ (T : Type) [Fintype T] [DecidableEq T] (tree : SimpleGraph T), tree.IsTree →
      ∀ (data : T → BagData V X) (root : T) (width choices : ℕ),
        RunningIntersection tree (fun t => (data t).bag) →
        (∀ t, (data t).Local) →
        (∀ t, (data t).bag.card ≤ width ∧ (data t).choices.card ≤ choices) →
        Fintype.card T ≤ m → ∃ p, Realization data root width choices p := by
  classical
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro T ft dt tree ht data root width choices hri hlocal hbound hcard
    let I := ↥(PartialDecompositions.components tree {root})
    have hcomp (C : I) : IsFlap tree {root} C.val := mem_components.mp C.property
    have hex : ∀ C : I, ∃ c : T, c ∈ C.val ∧ tree.Adj root c := by
      intro C
      obtain ⟨c,hc,ha,_⟩ := root_component_unique_neighbor ht (hcomp C)
      exact ⟨c,hc,ha⟩
    choose child hchild using hex
    have hplans : ∀ C : I, ∃ p, Realization (fun t : ↥C.val => data t.val)
        ⟨child C,(hchild C).1⟩ width choices p := by
      intro C
      have hlt : C.val.card < m := lt_of_lt_of_le (root_component_card_lt (hcomp C)) hcard
      have htree : (tree.induce (C.val : Set T)).IsTree :=
        ⟨(hcomp C).connected.induce_connected, ht.isAcyclic.induce _⟩
      exact ih C.val.card hlt ↥C.val (tree.induce (C.val : Set T)) htree
        (fun t => data t.val) ⟨child C,(hchild C).1⟩ width choices
        (induced_running hri C.val) (fun t => hlocal t.val) (fun t => hbound t.val) (by simp)
    choose plans hplans using hplans
    let ps := Finset.univ.toList.map plans
    have hscope (C : I) : (plans C).scope = C.val.biUnion (fun t => (data t).bag) := by
      ext v
      rw [(hplans C).scope]
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨t,ht⟩; exact ⟨t.val,t.property,ht⟩
      · rintro ⟨t,ht,hv⟩; exact ⟨⟨t,ht⟩,hv⟩
    have hcoh : ∀ p ∈ ps, p.Coherent := by
      intro p hp
      obtain ⟨C,_,rfl⟩ := List.mem_map.mp hp
      exact (hplans C).coherent
    have hloc : ∀ p ∈ ps, p.Local := by
      intro p hp
      obtain ⟨C,_,rfl⟩ := List.mem_map.mp hp
      exact (hplans C).local_data
    have hbdry : ∀ p ∈ ps, p.scope ∩ (data root).bag ⊆ p.root.bag := by
      intro p hp
      obtain ⟨C,_,rfl⟩ := List.mem_map.mp hp
      rw [hscope C,(hplans C).root_bag]
      exact component_boundary ht hri (hcomp C) (hchild C).1 (hchild C).2
    have hpair : ps.Pairwise (fun p q => p.scope ∩ q.scope ⊆ (data root).bag) := by
      apply List.pairwise_map.mpr
      apply (List.nodup_iff_pairwise_ne.mp (Finset.nodup_toList (Finset.univ : Finset I))).imp
      intro C D hne
      rw [hscope C,hscope D]
      exact distinct_scopes ht hri (hcomp C) (hcomp D) (fun h => hne (Subtype.ext h))
    have hpb : ∀ p ∈ ps, p.AllData (fun d => d.bag.card ≤ width ∧ d.choices.card ≤ choices) := by
      intro p hp
      obtain ⟨C,_,rfl⟩ := List.mem_map.mp hp
      exact (hplans C).bound
    refine ⟨joinForest (data root) ps,⟨joinForest_coherent _ _ hcoh hbdry hpair,
      joinForest_local _ _ (hlocal root) hloc,joinForest_root_bag _ _,joinForest_root_choices _ _,
      ?_,?_,?_,?_,?_,?_,joinForest_bag_bounds _ _ _ _ (hbound root) hpb⟩⟩
    · intro v
      rw [mem_joinForest_scope]
      constructor
      · rintro (hv | ⟨p,hp,hv⟩)
        · exact ⟨root,hv⟩
        · obtain ⟨C,_,rfl⟩ := List.mem_map.mp hp
          obtain ⟨t,ht⟩ := (hplans C).scope v |>.mp hv
          exact ⟨t.val,ht⟩
      · rintro ⟨t,ht⟩
        by_cases htr : t = root
        · exact Or.inl (htr ▸ ht)
        · obtain ⟨C,hC,htC⟩ := component_exists tree {root} (by simpa using htr)
          refine Or.inr ⟨plans ⟨C,hC⟩,List.mem_map.mpr ⟨⟨C,hC⟩,by simp,rfl⟩,?_⟩
          exact (hplans ⟨C,hC⟩).scope v |>.mpr ⟨⟨t,htC⟩,ht⟩
    · intro a
      rw [joinForest_valid_iff]
      constructor
      · rintro ⟨hr,hp⟩ t
        by_cases htr : t = root
        · exact htr ▸ hr
        · obtain ⟨C,hC,htC⟩ := component_exists tree {root} (by simpa using htr)
          have hc := hp (plans ⟨C,hC⟩) (List.mem_map.mpr ⟨⟨C,hC⟩,by simp,rfl⟩)
          exact (hplans ⟨C,hC⟩).valid a |>.mp hc ⟨t,htC⟩
      · intro ha
        refine ⟨ha root,?_⟩
        intro p hp
        obtain ⟨C,_,rfl⟩ := List.mem_map.mp hp
        exact (hplans C).valid a |>.mpr (fun t => ha t.val)
    · intro whole
      rw [joinForest_choice_cover]
      constructor
      · rintro ⟨hr,hp⟩ t
        by_cases htr : t = root
        · exact htr ▸ hr
        · obtain ⟨C,hC,htC⟩ := component_exists tree {root} (by simpa using htr)
          have hc := hp (plans ⟨C,hC⟩) (List.mem_map.mpr ⟨⟨C,hC⟩,by simp,rfl⟩)
          exact (hplans ⟨C,hC⟩).choice_cover whole |>.mp hc ⟨t,htC⟩
      · intro ha
        refine ⟨ha root,?_⟩
        intro p hp
        obtain ⟨C,_,rfl⟩ := List.mem_map.mp hp
        exact (hplans C).choice_cover whole |>.mpr (fun t => ha t.val)
    · intro a
      rw [joinForest_count]
      change (data root).count a + ((Finset.univ.toList.map plans).map (fun p => p.totalCount a)).sum = _
      rw [List.map_map,sum_univ_list]
      simp only [Function.comp_apply,(hplans _).count]
      exact sum_components tree root (fun t => (data t).count a)
    · intro a
      rw [joinForest_weight]
      change (data root).weight a + ((Finset.univ.toList.map plans).map (fun p => p.totalWeight a)).sum = _
      rw [List.map_map,sum_univ_list]
      simp only [Function.comp_apply,(hplans _).weight]
      exact sum_components tree root (fun t => (data t).weight a)
    · rw [joinForest_nodes]
      have hp : 1 + ∑ C : I, Fintype.card ↥C.val = Fintype.card T := by
        simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Nat.cast_id] using
          sum_components tree root (fun _ => (1 : ℕ))
      have hn : (∑ C : I, (plans C).nodes) + Fintype.card I =
          2 * ∑ C : I, Fintype.card ↥C.val := by
        calc
          _ = ∑ C : I, ((plans C).nodes + 1) := by simp [Finset.sum_add_distrib]
          _ = ∑ C : I, 2 * Fintype.card ↥C.val := Finset.sum_congr rfl (fun C _ => (hplans C).nodes)
          _ = _ := (Finset.mul_sum _ _ _).symm
      dsimp [ps]
      rw [List.map_map,sum_univ_list]
      simp only [List.length_map,Finset.length_toList,Finset.card_univ,Function.comp_apply]
      omega
end StableMSR.Recovery.TreeDP.TreeConstruction
open StableMSR.Recovery.TreeDP
/-- A genuine finite tree decomposition admits an exact binary DP representation
with one original bag node and one neutral join per original tree edge. -/
theorem solution {V X T : Type} [DecidableEq V]
    [Fintype T] [DecidableEq T] (G : SimpleGraph V) (tree : SimpleGraph T)
    (data : T → BagData V X)
    (htd : RobertsonSeymour1986.GM5.IsTreeDecomposition G tree (fun t => (data t).bag))
    (root : T) (width choices : ℕ)
    (hlocal : ∀ t, (data t).Local)
    (hbound : ∀ t, (data t).bag.card ≤ width ∧ (data t).choices.card ≤ choices) :
    ∃ p : Plan V X,
      p.Coherent ∧ p.Local ∧ p.root.bag = (data root).bag ∧
      p.root.choices = (data root).choices ∧
      (∀ v, v ∈ p.scope) ∧
      (∀ whole : V → X,
        (p.AllValid whole ↔ ∀ t, (data t).valid whole) ∧
        (p.AllData (fun d => ∃ a ∈ d.choices, AgreeOn d.bag whole a) ↔
          ∀ t, ∃ a ∈ (data t).choices, AgreeOn (data t).bag whole a) ∧
        p.totalCount whole = ∑ t, (data t).count whole ∧
        p.totalWeight whole = ∑ t, (data t).weight whole) ∧
      p.nodes + 1 = 2 * Fintype.card T ∧
      p.AllData (fun d => d.bag.card ≤ width ∧ d.choices.card ≤ choices) := by
  obtain ⟨p,hp⟩ := TreeConstruction.realization_of_card (V := V) (X := X)
    (Fintype.card T) T tree htd.1 data root width choices htd.2.2.2 hlocal hbound le_rfl
  exact ⟨p,hp.coherent,hp.local_data,hp.root_bag,hp.root_choices,
    fun v => (hp.scope v).mpr (htd.2.1 v),
    fun whole => ⟨hp.valid whole,hp.choice_cover whole,hp.count whole,hp.weight whole⟩,
    hp.nodes,hp.bound⟩

