-- Prove2me | solution 1 for StableMSR.Recovery.SingleSearch.root_component_geometry
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T00:12:17.826646+00:00
-- url     : https://prove2.me/submissions/328bae9e-bb8f-4100-b87e-96bc8551354f

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

end StableMSR.Recovery.DecompositionSearch
theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    let K:=PartialDecompositions.components G ∅
    K.biUnion id=Finset.univ ∧ (∀C∈K,boundary G C=∅) ∧
    ∀C∈K,∀E∈K,C≠E → Disjoint C E ∧ ∀u∈C,∀v∈E,¬G.Adj u v := by
  classical
  refine ⟨?_,?_,?_⟩
  · ext v;constructor
    · intro _;exact Finset.mem_univ v
    · intro _;exact Finset.mem_biUnion.mpr (component_exists G ∅ (Finset.notMem_empty v))
  · intro C hc;exact Finset.eq_empty_iff_forall_notMem.mpr (fun v hv=>Finset.notMem_empty v (boundary_subset (mem_components.mp hc) hv))
  · intro C hc E he ne
    have dis : Disjoint C E:=Finset.disjoint_left.mpr (fun v vc ve=>ne (components_eq_of_mem hc he vc ve))
    refine ⟨dis,?_⟩;intro u hu v hv edge
    exact Finset.disjoint_left.mp dis ((mem_components.mp hc).closed u hu v edge (Finset.notMem_empty v)) hv
