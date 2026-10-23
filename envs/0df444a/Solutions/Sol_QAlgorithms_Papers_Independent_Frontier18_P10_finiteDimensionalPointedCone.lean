-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P10.finiteDimensionalPointedCone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:24:07.131885+00:00
-- url     : https://prove2.me/submissions/ec4a6f06-3dce-4474-8b82-9e4907d1facc

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P10

noncomputable section

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal BigOperators

universe u v w

namespace QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Dependency50.P25

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperBorel

section x8

variable {d : ℕ}

lemma x8_add {C : Set (Fin d → ℝ)} (hcone : IsPointedCone C) {x y : Fin d → ℝ}
    (hx : x ∈ C) (hy : y ∈ C) : x + y ∈ C := by
  have h := hcone.2.1 hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  have := hcone.2.2.1 2 (by norm_num) _ h
  convert this using 1
  rw [smul_add, smul_smul, smul_smul]; norm_num

lemma x8_sum {C : Set (Fin d → ℝ)} (hcone : IsPointedCone C) {ι : Type*} (s : Finset ι)
    (f : ι → Fin d → ℝ) (hf : ∀ i ∈ s, f i ∈ C) : ∑ i ∈ s, f i ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hcone.1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact x8_add hcone (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- the compact pieces of the convex hull -/
def x8Φ (n : ℕ) : (Fin n → ℝ) × (Fin n → Fin d → ℝ) → (Fin d → ℝ) :=
  fun p => ∑ i, p.1 i • p.2 i

def x8U (S : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  ⋃ n ∈ Finset.range (d + 2), x8Φ n '' (stdSimplex ℝ (Fin n) ×ˢ Set.univ.pi (fun _ => S))

lemma x8_U_compact {S : Set (Fin d → ℝ)} (hS : IsCompact S) : IsCompact (x8U S) := by
  refine (Finset.range (d + 2)).isCompact_biUnion (fun n _ => ?_)
  refine IsCompact.image ((isCompact_stdSimplex ℝ (Fin n)).prod (isCompact_univ_pi (fun _ => hS))) ?_
  unfold x8Φ
  fun_prop

lemma x8_hull_eq (S : Set (Fin d → ℝ)) : convexHull ℝ S = x8U S := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨ι, _, z, w, hz, hai, hw, hw1, hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
    have hcard : Fintype.card ι ≤ d + 1 := by
      have := hai.card_le_finrank_succ
      have h2 := Submodule.finrank_le (vectorSpan ℝ (range z))
      rw [Module.finrank_fin_fun] at h2
      omega
    set n := Fintype.card ι
    let e := Fintype.equivFin ι
    simp only [x8U, mem_iUnion, Finset.mem_range]
    refine ⟨n, by omega, (fun j => w (e.symm j), fun j => z (e.symm j)), ⟨⟨fun j => (hw _).le, ?_⟩,
      fun j _ => hz (mem_range_self _)⟩, ?_⟩
    · rw [← hw1]; exact Equiv.sum_comp e.symm w
    · rw [← hx]; exact Equiv.sum_comp e.symm (fun i => w i • z i)
  · intro x hx
    simp only [x8U, mem_iUnion, Finset.mem_range] at hx
    obtain ⟨n, _, ⟨p, hp, rfl⟩⟩ := hx
    obtain ⟨⟨hp0, hp1⟩, hpS⟩ := hp
    exact (convex_convexHull ℝ S).sum_mem (fun i _ => hp0 i) hp1
      (fun i _ => subset_convexHull ℝ S (hpS i (mem_univ _)))

lemma x8_functional (C : Set (Fin d → ℝ)) (hclosed : IsClosed C) (hcone : IsPointedCone C) :
    ∃ (f : StrongDual ℝ (Fin d → ℝ)) (s : ℝ), 0 < s ∧ ∀ x ∈ C, s * ‖x‖ ≤ f x := by
  set S := C ∩ Metric.sphere (0 : Fin d → ℝ) 1
  have hS : IsCompact S := (isCompact_sphere 0 1).inter_left hclosed
  have h0 : (0 : Fin d → ℝ) ∉ convexHull ℝ S := by
    rw [x8_hull_eq]
    intro h
    simp only [x8U, mem_iUnion, Finset.mem_range] at h
    obtain ⟨n, _, ⟨p, hp, hp0⟩⟩ := h
    obtain ⟨⟨hpn, hp1⟩, hpS⟩ := hp
    obtain ⟨j, _, hj⟩ : ∃ j ∈ Finset.univ, p.1 j ≠ 0 := by
      by_contra hc; push_neg at hc
      rw [Finset.sum_eq_zero (fun j _ => hc j (Finset.mem_univ j))] at hp1; norm_num at hp1
    have hzj := hpS j (mem_univ _)
    have hjC : p.1 j • p.2 j ∈ C := hcone.2.2.1 _ (hpn j) _ hzj.1
    have hrest : ∑ i ∈ Finset.univ.erase j, p.1 i • p.2 i ∈ C :=
      x8_sum hcone _ _ (fun i _ => hcone.2.2.1 _ (hpn i) _ (hpS i (mem_univ _)).1)
    have hsplit := Finset.add_sum_erase Finset.univ (fun i => p.1 i • p.2 i) (Finset.mem_univ j)
    have hneg : -(p.1 j • p.2 j) = ∑ i ∈ Finset.univ.erase j, p.1 i • p.2 i := by
      have : x8Φ n p = ∑ i, p.1 i • p.2 i := rfl
      rw [← hsplit] at this; rw [hp0] at this
      exact neg_eq_of_add_eq_zero_right this.symm
    have hz : p.1 j • p.2 j = 0 := hcone.2.2.2 _ hjC (hneg ▸ hrest)
    rcases smul_eq_zero.1 hz with h | h
    · exact hj h
    · have := hzj.2; rw [h, mem_sphere_iff_norm, sub_zero, norm_zero] at this; norm_num at this
  have hcl : IsClosed (convexHull ℝ S) := by
    rw [x8_hull_eq]; exact (x8_U_compact hS).isClosed
  obtain ⟨f, s, hf0, hf⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ S) hcl h0
  rw [map_zero] at hf0
  refine ⟨f, s, hf0, fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · rw [hx0, norm_zero, mul_zero, map_zero]
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hxS : ‖x‖⁻¹ • x ∈ S := by
    refine ⟨hcone.2.2.1 _ (inv_nonneg.2 hn.le) _ hx, ?_⟩
    rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have := (hf _ (subset_convexHull ℝ S hxS)).le
  rw [map_smul, smul_eq_mul] at this
  have h2 := mul_le_mul_of_nonneg_left this hn.le
  rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul] at h2
  linarith

lemma x8_main (C : Set (Fin d → ℝ))
    (hclosed : IsClosed C) (hcone : IsPointedCone C) :
    GeneralizedMuCompact C := by
  classical
  unfold GeneralizedMuCompact
  refine ⟨hcone.2.1, hclosed, fun K hKC hK ε hε => ?_⟩
  obtain ⟨f, s, hs, hf⟩ := x8_functional C hclosed hcone
  obtain ⟨M0, hM0⟩ := hK.bddAbove_image f.continuous.continuousOn
  set M := max M0 1
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKM : ∀ y ∈ K, f y ≤ M := fun y hy => le_trans (hM0 (mem_image_of_mem f hy)) (le_max_left _ _)
  set R := M / (s * ε)
  refine ⟨C ∩ Metric.closedBall 0 R, inter_subset_left,
    (isCompact_closedBall 0 R).inter_left hclosed, fun e he => ?_⟩
  have hfe : ∑ i, e.weight i * f (e.point i) ≤ M := by
    have := hKM _ he
    unfold finiteMean at this
    rw [map_sum] at this
    simpa [map_smul, smul_eq_mul] using this
  have hpt : ∀ i, (if e.point i ∈ C ∩ Metric.closedBall 0 R then 0 else e.weight i) * (M / ε) ≤
      e.weight i * f (e.point i) := by
    intro i
    have hfi := hf _ (e.mem i)
    split_ifs with h
    · rw [zero_mul]
      exact mul_nonneg (e.nonnegative i) (le_trans (mul_nonneg hs.le (norm_nonneg _)) hfi)
    · have hout : R < ‖e.point i‖ := by
        by_contra hc; push_neg at hc
        exact h ⟨e.mem i, by rw [Metric.mem_closedBall, dist_zero_right]; exact hc⟩
      refine mul_le_mul_of_nonneg_left ?_ (e.nonnegative i)
      have : s * R = M / ε := by simp only [R]; field_simp
      nlinarith
  have hsum := le_trans (Finset.sum_le_sum (fun i _ => hpt i)) hfe
  rw [← Finset.sum_mul] at hsum
  have hout : ∑ i, (if e.point i ∈ C ∩ Metric.closedBall 0 R then 0 else e.weight i) ≤ ε := by
    have h2 : (∑ i, (if e.point i ∈ C ∩ Metric.closedBall 0 R then 0 else e.weight i)) * M ≤ ε * M := by
      have := mul_le_mul_of_nonneg_left hsum hε.le
      have e2 : ε * ((∑ i, (if e.point i ∈ C ∩ Metric.closedBall 0 R then 0 else e.weight i)) *
          (M / ε)) = (∑ i, (if e.point i ∈ C ∩ Metric.closedBall 0 R then 0 else e.weight i)) * M := by
        field_simp
      linarith
    exact le_of_mul_le_mul_right h2 hM
  have htot : ∑ i, (if e.point i ∈ C ∩ Metric.closedBall 0 R then e.weight i else 0) +
      ∑ i, (if e.point i ∈ C ∩ Metric.closedBall 0 R then 0 else e.weight i) = 1 := by
    rw [← Finset.sum_add_distrib, ← e.total]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> simp
  refine le_trans (by linarith : 1 - ε ≤ ∑ i, (if e.point i ∈ C ∩ Metric.closedBall 0 R then e.weight i else 0))
    (le_of_eq (Finset.sum_congr rfl (fun i _ => ?_)))
  split_ifs <;> rfl

end x8

end QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Frontier18.P10 in
open QAlgorithms.Papers.Independent.Dependency50.P25 in
attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperMeasurable in
attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperBorel in
theorem solution (d : ℕ) (C : Set (Fin d → ℝ))
    (hclosed : IsClosed C) (hcone : IsPointedCone C) :
    GeneralizedMuCompact C :=
  x8_main C hclosed hcone
