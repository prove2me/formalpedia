-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.exists_pendant_geodesic_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:35:25.5098+00:00
-- url     : https://prove2.me/submissions/f358fad7-9ac3-4e26-9c10-9565f64a90e5

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_reachable_compl_of_mem_geodesic
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_exists_two_adj_of_connected_deletions
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_outside_component_attachment
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_shallow_geodesic_meets_core

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (hG : G.Connected)
    (K : Finset α) (hcard : 3 ≤ K.card) (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (huniq : ∀ (z w : ↥((K : Set α)ᶜ)),
      (G.induce (K : Set α)ᶜ).Reachable z w →
      ∀ {a b : α}, a ∈ K → b ∈ K → G.Adj a z → G.Adj b w → a = b)
    (htwo : ∀ c, ¬ (G.induce ({c}ᶜ : Set α)).Connected →
      ∃ a b : ↥({c}ᶜ : Set α), ∃ q : G.Walk c (b : α),
        q.length = G.dist c b ∧
        ¬ (G.induce ({c}ᶜ : Set α)).Reachable a b ∧
        G.dist c b + 2 ≤ G.dist c a ∧
        ∀ z, z ∈ cutSide G c a ∨ z ∈ q.support) :
    Nonempty (PendantGeodesics G K) := by
  classical
  have hpaths (c : ↥(K : Set α)) :
      ∃ (e : α) (p : G.Walk c e),
        p.length = G.dist c e ∧
        (∀ z ∈ p.support, z ∈ K → z = (c : α)) ∧
        (∀ z ∈ p.support, z ≠ (c : α) → ∀ w, G.Adj z w → w ∈ p.support) ∧
        (∀ (z : ↥({(c : α)}ᶜ : Set α)), (z : α) ∉ p.support →
          ∀ (v : α) (hv : v ∈ K) (hvc : v ≠ (c : α)),
            (G.induce ({(c : α)}ᶜ : Set α)).Reachable z ⟨v, by simpa using hvc⟩) ∧
        (0 < p.length → ∃ a, p.length + 2 ≤ G.dist c a) := by
    by_cases hc : (G.induce ({(c : α)}ᶜ : Set α)).Connected
    · refine ⟨c, Walk.nil, by simp, ?_, ?_, ?_, ?_⟩
      · intro z hz _
        simpa using hz
      · intro z hz hzc
        exact (hzc (by simpa using hz)).elim
      · intro z _ v _ hvc
        exact hc z ⟨v, by simpa using hvc⟩
      · simp
    · obtain ⟨a, b, q, hq, hsep, hgap, hcover⟩ := htwo c hc
      obtain ⟨hside, hcore⟩ := shallow_geodesic_meets_core hG K hcard hK hdel
        c c.property a b q hq hsep hcover
      refine ⟨b, q, hq, hcore, ?_, ?_, ?_⟩
      · intro z hz hzc w hzw
        by_contra hwq
        have hwside := (hcover w).resolve_right hwq
        have hwc : w ≠ (c : α) := fun heq => hwq (heq ▸ q.start_mem_support)
        have hzb := reachable_compl_of_mem_geodesic q hq b.property hz hzc
        rcases hwside with heq | ⟨_, haw⟩
        · exact hwc heq
        · have hwz : (G.induce ({(c : α)}ᶜ : Set α)).Adj
              ⟨w, by simpa using hwc⟩ ⟨z, by simpa using hzc⟩ := hzw.symm
          exact hsep (haw.trans (hwz.reachable.trans hzb))
      · intro z hzq v hv hvc
        have hzside := (hcover z).resolve_right hzq
        rcases hzside with hzc | ⟨_, haz⟩
        · exact (z.property hzc).elim
        rcases hside v hv with heq | ⟨_, hav⟩
        · exact (hvc heq).elim
        · exact haz.symm.trans hav
      · intro _
        exact ⟨a, hq ▸ hgap⟩
  choose e P hgeo hcore hclosed hrest hgap using hpaths
  refine ⟨⟨e, P, hgeo, hcore, hclosed, hrest, hgap, ?_⟩⟩
  intro z
  by_cases hzK : z ∈ K
  · exact ⟨⟨z, hzK⟩, (P ⟨z, hzK⟩).start_mem_support⟩
  · obtain ⟨c, hc, w, hzw, hcw, hsep⟩ := outside_component_attachment hG K
      (Finset.card_pos.mp (by omega)) huniq ⟨z, hzK⟩
    obtain ⟨v, _, hcv, _, _⟩ := exists_two_adj_of_connected_deletions
      (G := G.induce (K : Set α)) (by simpa using hcard) hK hdel ⟨c, hc⟩
    have hvc : (v : α) ≠ c := (show G.Adj c v from hcv).ne.symm
    refine ⟨⟨c, hc⟩, ?_⟩
    by_contra hzP
    exact hsep v v.property hvc
      (hrest ⟨c, hc⟩ ⟨z, by simpa using (show z ≠ c from fun heq => hzK (heq.symm ▸ hc))⟩
        hzP v v.property hvc)
end WrittenOnTheWallII.GraphConjecture84
