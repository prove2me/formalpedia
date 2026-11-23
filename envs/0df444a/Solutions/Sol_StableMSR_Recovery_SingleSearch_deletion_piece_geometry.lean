-- Prove2me | solution 1 for StableMSR.Recovery.SingleSearch.deletion_piece_geometry
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T00:12:11.963047+00:00
-- url     : https://prove2.me/submissions/320de7f3-3c21-4bee-8666-84ef5153b40b

import Definitions.Def_StableMSR_SingleVertexSearch
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
open StableMSR.Recovery StableMSR.Recovery.Havens StableMSR.Recovery.PartialDecompositions
open StableMSR.Recovery.DecompositionSearch StableMSR.Recovery.WindowCuts StableMSR.Recovery.SingleSearch
open RobertsonSeymour1986.GM5
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

end StableMSR.Recovery.DecompositionSearch
theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S C B : Finset V)
    (hc : IsFlap G S C) (sb : S⊆B) (bc : B⊆S∪C) :
    let K:=children G B C
    K.biUnion id=C\B ∧ total B K=S∪C ∧
    (∀E∈K,IsFlap G (boundary G E) E ∧ Disjoint E B ∧ boundary G E⊆B ∧ rim G (S∪C) E=boundary G E) ∧
    ∀E∈K,∀F∈K,E≠F → Disjoint E F ∧ ∀u∈E,∀v∈F,¬G.Adj u v := by
  classical
  let K:=children G B C
  have cover : K.biUnion id=C\B:=children_partition hc sb
  have allU : total B K=S∪C:=by
    unfold total;rw [cover]
    apply Finset.Subset.antisymm
    · intro v hv;rcases Finset.mem_union.mp hv with h|h
      · exact bc h
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp h).1
    · intro v hv;by_cases hb : v∈B
      · exact Finset.mem_union_left _ hb
      · rcases Finset.mem_union.mp hv with h|h
        · exact (hb (sb h)).elim
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h,hb⟩)
  refine ⟨cover,allU,?_,?_⟩
  · intro E he
    have hf:=(mem_children.mp he).1
    refine ⟨flap_at_boundary hf,hf.avoids.symm,boundary_subset hf,?_⟩
    ext v;constructor
    · intro hv;exact mem_boundary.mpr (Finset.mem_filter.mp hv).2
    · intro hv;exact Finset.mem_filter.mpr ⟨bc (boundary_subset hf hv),mem_boundary.mp hv⟩
  · intro E he F hf ne
    have dis:=children_disjoint he hf ne
    refine ⟨dis,?_⟩;intro u hu v hv edge
    have vb : v∉B:=fun h=>Finset.disjoint_left.mp (mem_children.mp hf).1.avoids h hv
    exact Finset.disjoint_left.mp dis ((mem_children.mp he).1.closed u hu v edge vb) hv
