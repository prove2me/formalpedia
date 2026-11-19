-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.lemma_3_8
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:41:08.864564+00:00
-- url     : https://prove2.me/submissions/758e7384-b932-4d58-9389-8aef79d57892

import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_matching_mobius_factorization
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_3_15
set_option autoImplicit false
namespace QuantumBipartiteTesting.Bipartiteness
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency.types false

private lemma adj_symm {N c : ℕ} (F : Finset (ColoredEdge N c)) : Symmetric (Adj F) := by
  intro u v h
  obtain ⟨e, he, h | h⟩ := h
  · exact ⟨e, he, Or.inr h⟩
  · exact ⟨e, he, Or.inl h⟩

private lemma reach_symm {N c : ℕ} (F : Finset (ColoredEdge N c)) {u v : Fin N}
    (h : Relation.ReflTransGen (Adj F) u v) : Relation.ReflTransGen (Adj F) v u := by
  induction h with
  | refl => exact .refl
  | tail h hvw ih => exact (Relation.ReflTransGen.single (adj_symm F hvw)).trans ih

private def reachSetoid {N c : ℕ} (F : Finset (ColoredEdge N c)) : Setoid (Fin N) where
  r := Relation.ReflTransGen (Adj F)
  iseqv := ⟨fun _ => .refl, fun h => reach_symm F h, fun h h' => h.trans h'⟩

private def fullClass {N c : ℕ} (F : Finset (ColoredEdge N c)) (u : Fin N) : Finset (Fin N) :=
  univ.filter fun v => Relation.ReflTransGen (Adj F) u v

private lemma mem_fullClass {N c : ℕ} (F : Finset (ColoredEdge N c)) (u v : Fin N) :
    v ∈ fullClass F u ↔ Relation.ReflTransGen (Adj F) u v := by
  simp [fullClass]

private lemma self_fullClass {N c : ℕ} (F : Finset (ColoredEdge N c)) (u : Fin N) :
    u ∈ fullClass F u := (mem_fullClass F u u).mpr .refl

private lemma fullClass_eq_iff {N c : ℕ} (F : Finset (ColoredEdge N c)) (u v : Fin N) :
    fullClass F u = fullClass F v ↔ Relation.ReflTransGen (Adj F) u v := by
  constructor
  · intro h
    rw [← mem_fullClass F u v, h]
    exact self_fullClass F v
  · intro h
    ext w
    simp only [mem_fullClass]
    exact ⟨fun hw => (reach_symm F h).trans hw, fun hw => h.trans hw⟩

private lemma adj_incident {N c : ℕ} (F : Finset (ColoredEdge N c)) {u v : Fin N}
    (h : Adj F u v) : u ∈ Vertices F ∧ v ∈ Vertices F := by
  obtain ⟨e, he, h | h⟩ := h
  · exact ⟨by simp only [Vertices, mem_filter, mem_univ, true_and]; exact ⟨e,he,Or.inl h.1⟩,
      by simp only [Vertices, mem_filter, mem_univ, true_and]; exact ⟨e,he,Or.inr h.2⟩⟩
  · exact ⟨by simp only [Vertices, mem_filter, mem_univ, true_and]; exact ⟨e,he,Or.inr h.2⟩,
      by simp only [Vertices, mem_filter, mem_univ, true_and]; exact ⟨e,he,Or.inl h.1⟩⟩

private lemma reach_incident {N c : ℕ} (F : Finset (ColoredEdge N c)) {u v : Fin N}
    (hu : u ∈ Vertices F) (h : Relation.ReflTransGen (Adj F) u v) : v ∈ Vertices F := by
  induction h with
  | refl => exact hu
  | @tail v w h hvw ih => exact (adj_incident F hvw).2

private lemma isolated_class {N c : ℕ} (F : Finset (ColoredEdge N c)) {u : Fin N}
    (hu : u ∉ Vertices F) : fullClass F u = {u} := by
  ext v
  simp only [mem_fullClass, mem_singleton]
  constructor
  · intro h
    induction h with
    | refl => rfl
    | @tail v w h hvw ih => exact (hu (ih ▸ (adj_incident F hvw).1)).elim
  · rintro rfl
    exact .refl

private lemma component_fullClass {N c : ℕ} (F : Finset (ColoredEdge N c)) {u : Fin N}
    (hu : u ∈ Vertices F) :
    (Vertices F).filter (fun v => Relation.ReflTransGen (Adj F) u v) = fullClass F u := by
  ext v
  simp only [mem_filter, mem_fullClass]
  exact ⟨And.right, fun h => ⟨reach_incident F hu h, h⟩⟩


private lemma componentAt_eq {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (i : Fin (Components F).card) :
    ComponentAt F i = (Components F).toList[i.val]'(by simpa using i.isLt) := by
  have hi : i.val < (Components F).toList.length := by simpa only [length_toList] using i.isLt
  unfold ComponentAt
  rw [List.getElem?_eq_getElem hi]
  rfl

private lemma componentAt_mem {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (i : Fin (Components F).card) : ComponentAt F i ∈ Components F := by
  rw [componentAt_eq]
  exact mem_toList.mp (List.getElem_mem _)

private lemma componentAt_injective {N colors : ℕ} (F : Finset (ColoredEdge N colors)) :
    Function.Injective (ComponentAt F) := by
  intro i j h
  simp only [componentAt_eq] at h
  exact Fin.ext ((Components F).nodup_toList.getElem_inj_iff.mp h)

private lemma componentAt_surjective {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (S : Finset (Fin N)) (hS : S ∈ Components F) : ∃ i, ComponentAt F i = S := by
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem (mem_toList.mpr hS)
  refine ⟨⟨i,by simpa using hi⟩,?_⟩
  rw [componentAt_eq]
  exact he

private lemma sum_componentAt {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (f : Finset (Fin N) → ℕ) :
    (∑ i : Fin (Components F).card, f (ComponentAt F i)) = ∑ S ∈ Components F, f S := by
  apply Finset.sum_bij (fun i _ => ComponentAt F i)
  · intro i hi; exact componentAt_mem F i
  · intro i hi j hj hij; exact componentAt_injective F hij
  · intro S hS; obtain ⟨i,hi⟩ := componentAt_surjective F S hS; exact ⟨i,mem_univ _,hi⟩
  · intros; rfl

private lemma component_containing {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (u : Fin N) (hu : u ∈ Vertices F) (S : Finset (Fin N)) (hS : S ∈ Components F) :
    u ∈ S ↔ S = fullClass F u := by
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hS
  rw [component_fullClass F hv,mem_fullClass]
  constructor
  · intro h; exact (fullClass_eq_iff F v u).mpr h
  · intro h; exact (fullClass_eq_iff F v u).mp h

private lemma component_counts {N colors : ℕ} (F : Finset (ColoredEdge N colors)) :
    (∑ i, ∑ j : Fin colors, ComponentColorCount F i j) = F.card := by
  unfold ComponentColorCount
  rw [sum_componentAt F (fun S => ∑ j : Fin colors, (F.filter (fun e => e.1 ∈ S ∧ e.2.2 = j)).card)]
  simp_rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; intro j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have hu : e.1 ∈ Vertices F := by
    simp only [Vertices,mem_filter,mem_univ,true_and]
    exact ⟨e,he,Or.inl rfl⟩
  have hc : fullClass F e.1 ∈ Components F := by
    exact mem_image.mpr ⟨e.1,hu,component_fullClass F hu⟩
  rw [Finset.sum_comm]
  have hh (S : Finset (Fin N)) :
      (∑ j : Fin colors, if e.1 ∈ S ∧ e.2.2 = j then 1 else 0) = if e.1 ∈ S then 1 else 0 := by
    by_cases h : e.1 ∈ S <;> simp [h]
  simp_rw [hh]
  have hi : (∑ S ∈ Components F, if e.1 ∈ S then 1 else 0) =
      ∑ S ∈ Components F, if S = fullClass F e.1 then 1 else 0 := by
    apply sum_congr rfl
    intro S hS
    simp only [component_containing F e.1 hu S hS]
  rw [hi]
  simp [hc]

private lemma topology_factorization {N colors : ℕ} (q : ℕ) (F : Finset (ColoredEdge N colors))
    (he : F.card ≤ 2*q) : ∃ B : Bivariate, B.totalDegree ≤ DenominatorDegree q ∧
      ∀ M l : ℝ, l ≠ 0 → Eval (Denominator q) M l ≠ 0 →
        TopologyMoment F M l = l ^ CycleRank F * Eval B M l / Eval (Denominator q) M l := by
  have hd : (∑ i, ∑ j, ComponentColorCount F i j) ≤ 2*q := by
    rw [component_counts]
    exact he
  choose H hdeg hH using (fun p => matching_mobius_factorization (ComponentColorCount F) q hd p)
  refine ⟨∑ p, H p,MvPolynomial.totalDegree_finsetSum_le (fun p hp => hdeg p),?_⟩
  intro M l hl hden
  unfold TopologyMoment
  simp only [PartitionCorrection,PartitionMoment] at hH ⊢
  simp_rw [hH _ M l hl hden,component_counts]
  simp only [← mul_div_assoc]
  rw [← Finset.sum_div]
  congr 1
  simp only [Eval,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hb : (Blocks p).card ≤ (Components F).card := by
    unfold Blocks
    exact Finset.card_image_le.trans_eq (by simp)
  have heq : (((F.card+(Components F).card-(Blocks p).card:ℕ):ℤ)) =
      (F.card:ℤ)+(Components F).card-(Blocks p).card := by
    omega
  rw [← zpow_natCast,← mul_assoc,← zpow_add₀ hl,heq]
  congr 2
  unfold CycleRank
  ring


end
end QuantumBipartiteTesting.Bipartiteness

open QuantumBipartiteTesting.Bipartiteness
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution : ∃ Cdeg : ℝ, 0 < Cdeg ∧
    ∀ N q : ℕ, ∀ F : Finset (ColoredEdge N), Consistent F → F.card ≤ 2*q →
    ∃ B : Bivariate, (B.totalDegree : ℝ) ≤ Cdeg * DegreeScale q ∧
      ∀ M l : ℝ, l ≠ 0 → Eval (Denominator q) M l ≠ 0 →
        TopologyMoment F M l = l ^ CycleRank F * Eval B M l / Eval (Denominator q) M l := by
  obtain ⟨C,hC,hbound⟩ := lemma_3_15.1
  refine ⟨C,hC,?_⟩
  intro N q F hF he
  obtain ⟨B,hdeg,hB⟩ := topology_factorization q F he
  refine ⟨B,?_,hB⟩
  have hd : DenominatorDegree q ≤ TruncationDegree q := by unfold TruncationDegree; omega
  exact (Nat.cast_le.mpr (hdeg.trans hd)).trans (hbound q)
end
