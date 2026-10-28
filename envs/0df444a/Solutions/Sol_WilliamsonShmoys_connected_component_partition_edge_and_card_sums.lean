-- Prove2me | solution 1 for WilliamsonShmoys.connected_component_partition_edge_and_card_sums
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T11:30:18.05568+00:00
-- url     : https://prove2.me/submissions/0e0a27ef-acc4-4bed-b72d-1911042bd162

import Mathlib

namespace S84CC

variable {V : Type} [Fintype V]

def E (G : SimpleGraph V) (S : Set V) : Set (Sym2 V) := G.edgeSet ∩ {e | ∀ v ∈ e, v ∈ S}

theorem ncard_induce (G : SimpleGraph V) (S : Set V) :
    (G.induce S).edgeSet.ncard = (E G S).ncard := by
  have hinj : Function.Injective (Sym2.map (Subtype.val : S → V)) :=
    Sym2.map.injective Subtype.val_injective
  rw [← Set.ncard_image_of_injective _ hinj]
  congr 1
  ext e
  constructor
  · rintro ⟨f, hf, rfl⟩
    induction f using Sym2.ind with
    | _ x y =>
    simp only [Sym2.map_pair_eq, E, Set.mem_inter_iff, SimpleGraph.mem_edgeSet, Set.mem_setOf_eq,
      Sym2.mem_iff] at hf ⊢
    refine ⟨by simpa using hf, ?_⟩
    rintro v (rfl | rfl)
    · exact x.2
    · exact y.2
  · induction e using Sym2.ind with
    | _ a b =>
    rintro ⟨h1, h2⟩
    have ha : a ∈ S := h2 a (Sym2.mem_mk_left a b)
    have hb : b ∈ S := h2 b (Sym2.mem_mk_right a b)
    exact ⟨s(⟨a, ha⟩, ⟨b, hb⟩), by simpa using h1, by simp⟩

theorem comp_eq (K : SimpleGraph V) {e : Sym2 V} (he : e ∈ K.edgeSet) {v w : V}
    (hv : v ∈ e) (hw : w ∈ e) : K.connectedComponentMk v = K.connectedComponentMk w := by
  induction e using Sym2.ind with
  | _ a b =>
  rw [SimpleGraph.mem_edgeSet] at he
  rw [Sym2.mem_iff] at hv hw
  rw [SimpleGraph.ConnectedComponent.eq]
  rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
  · rfl
  · exact he.reachable
  · exact he.symm.reachable
  · rfl

theorem card_sum (K : SimpleGraph V) [Fintype K.ConnectedComponent] :
    ∑ c : K.ConnectedComponent, c.supp.ncard = Fintype.card V := by
  classical
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := K.connectedComponentMk)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Set.ncard_coe_finset]; congr 1; ext v
  simp [SimpleGraph.ConnectedComponent.mem_supp_iff]

theorem edge_sum (K : SimpleGraph V) [Fintype K.ConnectedComponent] :
    K.edgeSet.ncard = ∑ c : K.ConnectedComponent, (K.induce c.supp).edgeSet.ncard := by
  classical
  simp_rw [ncard_induce]
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset,
    Finset.card_eq_sum_card_fiberwise (f := fun e : Sym2 V => K.connectedComponentMk e.out.1)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Set.ncard_coe_finset]; congr 1; ext e
  simp only [Finset.coe_filter, SimpleGraph.mem_edgeFinset, E, Set.mem_inter_iff, Set.mem_setOf_eq,
    SimpleGraph.ConnectedComponent.mem_supp_iff]
  constructor
  · rintro ⟨he, hc⟩
    refine ⟨he, fun v hv => ?_⟩
    rw [← hc]; exact comp_eq K he hv (Sym2.out_fst_mem e)
  · rintro ⟨he, h⟩
    exact ⟨he, h _ (Sym2.out_fst_mem e)⟩

end S84CC

set_option autoImplicit false
namespace WilliamsonShmoys
theorem _root_.solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) :
    ∃ comps : Finset (Set V),
      (∀ C ∈ comps, C.Nonempty) ∧
      (∀ C ∈ comps, ∀ D ∈ comps, C ≠ D → Disjoint C D) ∧
      (∀ v : V, ∃ C ∈ comps, v ∈ C) ∧
      (∀ C ∈ comps, (K.induce C).Connected) ∧
      (∑ C ∈ comps, C.ncard = Fintype.card V) ∧
      (K.edgeSet.ncard = ∑ C ∈ comps, (K.induce C).edgeSet.ncard) := by
  classical
  refine ⟨Finset.univ.image (fun c : K.ConnectedComponent => c.supp), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨c, rfl⟩
    exact ⟨c.out, by rw [SimpleGraph.ConnectedComponent.mem_supp_iff]; exact Quot.out_eq c⟩
  · simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩ hne
    rw [Set.disjoint_left]
    intro v hc hd
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hc hd
    exact hne (by rw [← hc, ← hd])
  · intro v
    exact ⟨(K.connectedComponentMk v).supp, Finset.mem_image_of_mem _ (Finset.mem_univ _), by simp [SimpleGraph.ConnectedComponent.mem_supp_iff]⟩
  · simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨c, rfl⟩
    exact (SimpleGraph.ConnectedComponent.maximal_connected_induce_supp c).prop
  · rw [Finset.sum_image (fun c _ d _ h => SimpleGraph.ConnectedComponent.supp_injective h)]
    exact S84CC.card_sum K
  · rw [Finset.sum_image (fun c _ d _ h => SimpleGraph.ConnectedComponent.supp_injective h)]
    exact S84CC.edge_sum K
end WilliamsonShmoys

