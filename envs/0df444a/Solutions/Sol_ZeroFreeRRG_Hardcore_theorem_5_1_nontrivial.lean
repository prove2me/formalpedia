-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.theorem_5_1_nontrivial
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T04:24:47.518166+00:00
-- url     : https://prove2.me/submissions/d1985e0a-e1ca-41b1-b0d3-777edd26ccb5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_Models
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Theorems.Thm_ZeroFreeRRG_Hardcore_cm_rssc_zero_free
import Theorems.Thm_ZeroFreeRRG_Hardcore_bethe_canonical_local
import Theorems.Thm_ZeroFreeRRG_Hardcore_cm_simple_to_regular

open scoped Classical
open Filter Topology AFIsingKS
open ZeroFreeRRG.Hardcore

theorem solution (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) :
    ∀ t : ℝ, m.Nontrivial t → Condition1 m d t → Condition2 m d t →
      ∃ U : Set ℂ, IsOpen U ∧ (t : ℂ) ∈ U ∧
        PottsRapidMixing.WithHighProb d (fun n G => ∀ z ∈ U, m.Zgraph d G z ≠ 0) := by
  intro t ht hC1 hC2
  obtain ⟨R₁, hR₁, hzero⟩ := cm_rssc_zero_free m hm d hd t ht hC1 hC2
  obtain ⟨R₂, hR₂, C, hC, hcanon⟩ := bethe_canonical_local m hm d hd t ht
  let R : ℝ := min R₁ R₂
  let U : Set ℂ := Metric.ball (t : ℂ) R
  have hR : 0 < R := lt_min hR₁ hR₂
  refine ⟨U, Metric.isOpen_ball, ?_, ?_⟩
  · exact Metric.mem_ball_self hR
  · apply cm_simple_to_regular m d hd U
    have hprob_le_one (n : ℕ) (P : Matching n d → Prop) : cmProb P ≤ 1 := by
      unfold cmProb
      by_cases hN : Fintype.card (Matching n d) = 0
      · simp [hN]
      · have hN' : 0 < (Fintype.card (Matching n d) : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hN
        rw [div_le_one hN']
        exact_mod_cast (Finset.card_le_card (Finset.subset_univ
          (Finset.univ.filter P)) : (Finset.univ.filter P).card ≤ Finset.univ.card)
    have hprob_mono {n : ℕ} {P Q : Matching n d → Prop}
        (hPQ : ∀ M, P M → Q M) : cmProb P ≤ cmProb Q := by
      unfold cmProb
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast Finset.card_le_card (show Finset.univ.filter P ⊆ Finset.univ.filter Q by
        intro M hM
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM ⊢
        exact hPQ M hM)
    have hbound (n : ℕ) :
        cmProb (fun M : Matching n d => IsSimpleM M →
          ∀ z ∈ Metric.closedBall (t : ℂ) R₁, normZ m z M ≠ 0) ≤
        cmProb (fun M : Matching n d => IsSimpleM M →
          ∀ z ∈ U, m.Zgraph d (toGraph M) z ≠ 0) := by
      apply hprob_mono
      intro M hM hMs z hz
      have hzR : z ∈ Metric.closedBall (t : ℂ) R := by
        apply Metric.mem_closedBall.mpr
        exact (Metric.mem_ball.mp hz).le
      have hzR₁ : z ∈ Metric.closedBall (t : ℂ) R₁ :=
        Metric.mem_closedBall.mpr ((Metric.mem_closedBall.mp hzR).trans (min_le_left _ _))
      have hzR₂ : z ∈ Metric.closedBall (t : ℂ) R₂ :=
        Metric.mem_closedBall.mpr ((Metric.mem_closedBall.mp hzR).trans (min_le_right _ _))
      rw [hcanon n M hMs z hzR₂]
      exact mul_ne_zero (pow_ne_zero n (hC z hzR₂)) (hM hMs z hzR₁)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hzero tendsto_const_nhds
      (Filter.Eventually.of_forall hbound)
      (Filter.Eventually.of_forall (fun n => hprob_le_one n _))
