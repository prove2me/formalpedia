-- Prove2me | solution 1 for SeymourThomas1993.haven_of_bramble
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T19:59:52.608149+00:00
-- url     : https://prove2.me/submissions/473c30c7-16da-446c-953b-f477e9605d97

import Definitions.Def_SeymourThomas1993_Brambles
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical
namespace StableMSR.Recovery.Havens

open TreewidthApprox.Pushed

variable {V : Type} [DecidableEq V]

/-- The component of `u` in the induced graph on `U`, as an ambient finset.
The intended use assumes `u ∈ U`; otherwise this definition is empty. -/
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

lemma ConnectedSet.induce_connected {G : SimpleGraph V} {C : Finset V}
    (hC : ConnectedSet G C) : (G.induce (C : Set V)).Connected := by
  refine { preconnected := ?_, nonempty := ?_ }
  · intro x y
    obtain ⟨p, hp⟩ := hC.2 x.val x.property y.val y.property
    exact ⟨p.induce (C : Set V) hp⟩
  · obtain ⟨x, hx⟩ := hC.1
    exact ⟨⟨x, hx⟩⟩

lemma componentWithin_induce_connected {G : SimpleGraph V} {U : Finset V} {u : V}
    (hu : u ∈ U) : (G.induce (componentWithin G U u : Set V)).Connected :=
  (componentWithin_connected hu).induce_connected

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

lemma componentWithin_no_edge (G : SimpleGraph V) (U : Finset V) (u : V) :
    NoEdge G (componentWithin G U u) (U \ componentWithin G U u) := by
  intro x hx y hy hxy
  exact (Finset.mem_sdiff.mp hy).2 (componentWithin_closed hx hxy (Finset.mem_sdiff.mp hy).1)

lemma componentWithin_ne_of_not_connected {G : SimpleGraph V} {U : Finset V} {u : V}
    (hu : u ∈ U) (hU : ¬ (G.induce (U : Set V)).Connected) : componentWithin G U u ≠ U := by
  intro heq
  exact hU (heq ▸ componentWithin_induce_connected hu)

/-- Every nonempty disconnected induced subgraph has a nonempty proper
connected component, closed under edges within that induced subgraph. -/
theorem exists_proper_component {G : SimpleGraph V} {U : Finset V}
    (hU : U.Nonempty) (hdisc : ¬ (G.induce (U : Set V)).Connected) :
    ∃ C : Finset V, C.Nonempty ∧ C ⊂ U ∧ (G.induce (C : Set V)).Connected ∧ NoEdge G C (U \ C) := by
  obtain ⟨u, hu⟩ := hU
  refine ⟨componentWithin G U u, ⟨u, self_mem_componentWithin hu⟩, ?_,
    componentWithin_induce_connected hu, componentWithin_no_edge G U u⟩
  exact Finset.ssubset_iff_subset_ne.mpr
    ⟨componentWithin_subset G U u, componentWithin_ne_of_not_connected hu hdisc⟩

end StableMSR.Recovery.Havens
namespace StableMSR.Recovery.Brambles
open Havens
lemma exists_flap_containing {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {W S : Finset V}
    (hS : ConnectedSet G S) (havoid : Disjoint W S) :
    ∃ C : Finset V, IsFlap G W C ∧ S ⊆ C := by
  classical
  obtain ⟨u,hu⟩ := hS.1
  have huW : u ∈ Wᶜ := Finset.mem_compl.mpr (fun h => Finset.disjoint_left.mp havoid h hu)
  refine ⟨componentWithin G Wᶜ u,⟨componentWithin_connected huW,?_,?_⟩,?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hvW hvC
    exact (Finset.mem_compl.mp (componentWithin_subset G Wᶜ u hvC)) hvW
  · intro x hx y hxy hy
    exact componentWithin_closed hx hxy (Finset.mem_compl.mpr hy)
  · intro v hv
    obtain ⟨p,hp⟩ := hS.2 u hu v hv
    refine mem_componentWithin.mpr ⟨Finset.mem_compl.mpr (fun h => Finset.disjoint_left.mp havoid h hv),p,?_⟩
    intro z hz
    exact Finset.mem_compl.mpr (fun h => Finset.disjoint_left.mp havoid h (hp z hz))

lemma touch_mono {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {S T C D : Finset V}
    (hSC : S ⊆ C) (hTD : T ⊆ D) (ht : Touch G S T) : Touch G C D := by
  rcases ht with ⟨v,hvS,hvT⟩ | ⟨u,hu,v,hv,huv⟩
  · exact Or.inl ⟨v,hSC hvS,hTD hvT⟩
  · exact Or.inr ⟨u,hSC hu,v,hTD hv,huv⟩

/-- Every bramble of order at least `k` defines a haven of order `k`. -/
theorem haven_of_bramble {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {family : Finset (Finset V)} {k : ℕ}
    (hB : IsBramble G family) (horder : OrderAtLeast family k) :
    ∃ β : Finset V → Finset V, Haven G k β := by
  classical
  have hex : ∀ W : Finset V, W.card < k →
      ∃ C : Finset V, IsFlap G W C ∧ ∃ S ∈ family, S ⊆ C := by
    intro W hW
    obtain ⟨S,hSB,havoid⟩ := horder W hW
    obtain ⟨C,hC,hSC⟩ := exists_flap_containing (hB.connected S hSB) havoid
    exact ⟨C,hC,S,hSB,hSC⟩
  let β : Finset V → Finset V := fun W => if h : W.card < k then Classical.choose (hex W h) else ∅
  have hβ : ∀ W, W.card < k → IsFlap G W (β W) ∧ ∃ S ∈ family, S ⊆ β W := by
    intro W hW
    dsimp [β]
    rw [dif_pos hW]
    exact Classical.choose_spec (hex W hW)
  refine ⟨β,⟨fun W hW => (hβ W hW).1,?_⟩⟩
  intro W W' hW hW'
  obtain ⟨S,hS,hSC⟩ := (hβ W hW).2
  obtain ⟨T,hT,hTD⟩ := (hβ W' hW').2
  exact touch_mono hSC hTD (hB.touch S hS T hT)
end StableMSR.Recovery.Brambles
open StableMSR.Recovery.Brambles StableMSR.Recovery.Havens
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {family : Finset (Finset V)} {k : ℕ}
    (hB : IsBramble G family) (horder : OrderAtLeast family k) :
    ∃ β : Finset V → Finset V, Haven G k β := by
  exact StableMSR.Recovery.Brambles.haven_of_bramble hB horder
