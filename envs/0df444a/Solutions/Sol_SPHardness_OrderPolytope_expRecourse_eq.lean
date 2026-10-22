-- Prove2me | solution 1 for SPHardness.OrderPolytope.expRecourse_eq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:16:27.986727+00:00
-- url     : https://prove2.me/submissions/eebf6510-1b5b-425e-9509-4623f692a74d

import Mathlib
import Definitions.Def_SPHardness_OrderPolytope_Model

set_option autoImplicit false
open SPHardness.OrderPolytope MeasureTheory

open Classical in
theorem S_ssv (P : Type) [Fintype P] [PartialOrder P]
    (ξ : P → ℝ) (hξ : ξ ∈ cube P) :
    secondStageValue P ξ = if ξ ∈ orderPolytope P then 0 else 1 := by
  classical
  by_cases hO : ξ ∈ orderPolytope P
  · rw [if_pos hO]
    have hset : {z | secondStageFeasible P ξ z} = {0} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨y, hy, hz0, hz1, hz⟩
        have hle : ∑ i : P, ∑ j : P, (if i ≤ j then (ξ i - ξ j) * y i j else 0) ≤ 0 := by
          refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
          split_ifs with h
          · exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hO.2 i j h]) (hy i j)
          · exact le_refl _
        linarith
      · rintro rfl
        exact ⟨fun _ _ => 0, fun _ _ => le_refl _, le_refl _, zero_le_one, by simp⟩
    unfold secondStageValue
    rw [hset]
    simp
  · rw [if_neg hO]
    obtain ⟨i, j, hij, hlt⟩ : ∃ i j : P, i ≤ j ∧ ξ j < ξ i := by
      by_contra hcon
      push Not at hcon
      exact hO ⟨hξ, fun i j h => hcon i j h⟩
    have hne : 0 < ξ i - ξ j := by linarith
    have hfeas : secondStageFeasible P ξ 1 := by
      refine ⟨fun a b => if a = i ∧ b = j then 1 / (ξ i - ξ j) else 0, fun a b => ?_,
        zero_le_one, le_refl _, ?_⟩
      · show 0 ≤ (if a = i ∧ b = j then 1 / (ξ i - ξ j) else 0)
        split_ifs
        · exact (one_div_pos.2 hne).le
        · exact le_refl _
      · rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
        · simp [hij]
          field_simp
          rfl
        · intro b _ hb
          simp [hb]
        · intro hj; exact absurd (Finset.mem_univ j) hj
        · intro a _ ha
          refine Finset.sum_eq_zero (fun b _ => ?_)
          simp [ha]
        · intro hi; exact absurd (Finset.mem_univ i) hi
    have hgr : IsGreatest {z : ℝ | secondStageFeasible P ξ z} 1 := by
      refine ⟨hfeas, ?_⟩
      rintro z ⟨y, hy, hz0, hz1, hz⟩
      exact hz1
    unfold secondStageValue
    exact hgr.csSup_eq

theorem solution (P : Type) [Fintype P] [PartialOrder P] : expRecourse P = 1 - volOrder P := by
  classical
  have hcm : MeasurableSet (cube P) := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hOm : MeasurableSet (orderPolytope P) := by
    have : orderPolytope P = cube P ∩ ⋂ i, ⋂ j, ⋂ (_ : i ≤ j), {ξ : P → ℝ | ξ i ≤ ξ j} := by
      ext ξ; simp [orderPolytope]
    rw [this]
    exact hcm.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j))
  have hOsub : orderPolytope P ⊆ cube P := fun ξ h => h.1
  have hvol : volume (cube P) = 1 := by
    unfold cube
    rw [volume_pi_pi]
    simp
  have hOle : volume (orderPolytope P) ≤ 1 := hvol ▸ measure_mono hOsub
  have hOne : volume (orderPolytope P) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hOle
  unfold expRecourse
  have h1 : ∫ ξ in cube P, secondStageValue P ξ =
      ∫ ξ in cube P, (orderPolytope P)ᶜ.indicator (1 : (P → ℝ) → ℝ) ξ := by
    refine setIntegral_congr_fun hcm (fun ξ hξ => ?_)
    rw [S_ssv P ξ hξ]
    by_cases h : ξ ∈ orderPolytope P <;> simp [h]
  rw [h1, integral_indicator_one hOm.compl, Measure.real, Measure.restrict_apply hOm.compl]
  have hd : (orderPolytope P)ᶜ ∩ cube P = cube P \ orderPolytope P := by
    ext ξ; simp [and_comm]
  rw [hd, measure_diff hOsub hOm.nullMeasurableSet hOne, hvol]
  unfold volOrder
  rw [ENNReal.toReal_sub_of_le hOle ENNReal.one_ne_top]
  simp
