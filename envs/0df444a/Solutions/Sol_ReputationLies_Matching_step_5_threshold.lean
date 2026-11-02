-- Prove2me | solution 1 for ReputationLies.Matching.step_5_threshold
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:59:07.534471+00:00
-- url     : https://prove2.me/submissions/06dba2f2-6600-48c3-8065-c67ac71855e5

import Mathlib
import Definitions.Def_ReputationLies_Matching_Model
import Theorems.Thm_ReputationLies_Matching_step_4_bayes_belief

open Set MeasureTheory ReputationLies.Matching

theorem solution (P : Primitives) (hP : P.Standing) :
    StrictMonoOn P.lieGain (Ioc 0 1) ∧ ContinuousOn P.lieGain (Ioc 0 1) ∧
    P.lieGain 1 = P.Bbar ∧
    ∀ ℓ : ℝ, 0 < ℓ → ℓ < P.Bbar → ∃! b : ℝ, b ∈ Ioo (0 : ℝ) 1 ∧ P.lieGain b = ℓ := by
  obtain ⟨-, hmono, hcont, h0, h1⟩ := step_4_bayes_belief P hP
  obtain ⟨hsL, hsLH, hsH1, hp0, hp1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hF, hFC⟩ := hP
  have hshat : P.sL < P.shat := by unfold Primitives.shat; nlinarith
  have hshat1 : P.shat < 1 := by unfold Primitives.shat; nlinarith
  -- range of sRof
  have hrange : ∀ b ∈ Ioc (0:ℝ) 1, P.sRof b ∈ Ioc P.sL 1 ∧ P.sRof b ∈ Icc (0:ℝ) 1 := by
    intro b hb
    have a1 : P.sRof 0 < P.sRof b := hmono ⟨le_rfl, zero_le_one⟩ ⟨hb.1.le, hb.2⟩ hb.1
    have a2 : P.sRof b ≤ P.sRof 1 := hmono.monotoneOn ⟨hb.1.le, hb.2⟩ ⟨zero_le_one, le_rfl⟩ hb.2
    rw [h0] at a1; rw [h1] at a2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hrangeI : ∀ b ∈ Icc (0:ℝ) 1, P.sRof b ∈ Icc (0:ℝ) 1 := by
    intro b hb
    have a1 : P.sRof 0 ≤ P.sRof b := hmono.monotoneOn ⟨le_rfl, zero_le_one⟩ hb hb.1
    have a2 : P.sRof b ≤ P.sRof 1 := hmono.monotoneOn hb ⟨zero_le_one, le_rfl⟩ hb.2
    rw [h0] at a1; rw [h1] at a2
    exact ⟨by linarith, by linarith⟩
  have hsLI : P.sL ∈ Icc (0:ℝ) 1 := ⟨hsL.le, by linarith⟩
  have hF0 : 0 ≤ P.F 0 := ENNReal.toReal_nonneg
  have hFsL : 0 < P.F P.sL := lt_of_le_of_lt hF0 (hF ⟨le_rfl, zero_le_one⟩ hsLI hsL)
  -- u = F ∘ sRof
  have hu_gt : ∀ b ∈ Ioc (0:ℝ) 1, P.F P.sL < P.F (P.sRof b) := fun b hb =>
    hF hsLI (hrange b hb).2 (hrange b hb).1.1
  have hu_mono : StrictMonoOn (fun b => P.F (P.sRof b)) (Ioc 0 1) := by
    intro a ha b hb hab
    exact hF (hrange a ha).2 (hrange b hb).2 (hmono ⟨ha.1.le, ha.2⟩ ⟨hb.1.le, hb.2⟩ hab)
  have hg : ∀ b ∈ Ioc (0:ℝ) 1, (P.F (P.sRof b) - P.F P.sL) / P.F (P.sRof b)
      = 1 - P.F P.sL / P.F (P.sRof b) := by
    intro b hb
    have : P.F (P.sRof b) ≠ 0 := by linarith [hu_gt b hb]
    field_simp
  have hgpos : ∀ b ∈ Ioc (0:ℝ) 1, 0 < (P.F (P.sRof b) - P.F P.sL) / P.F (P.sRof b) := by
    intro b hb
    have := hu_gt b hb
    exact div_pos (by linarith) (by linarith)
  have hgle : ∀ b ∈ Ioc (0:ℝ) 1, (P.F (P.sRof b) - P.F P.sL) / P.F (P.sRof b) ≤ 1 := by
    intro b hb
    rw [hg b hb]
    have := hu_gt b hb
    have : 0 ≤ P.F P.sL / P.F (P.sRof b) := div_nonneg hFsL.le (by linarith)
    linarith
  have hgmono : ∀ a ∈ Ioc (0:ℝ) 1, ∀ b ∈ Ioc (0:ℝ) 1, a < b →
      (P.F (P.sRof a) - P.F P.sL) / P.F (P.sRof a) <
        (P.F (P.sRof b) - P.F P.sL) / P.F (P.sRof b) := by
    intro a ha b hb hab
    rw [hg a ha, hg b hb]
    have := hu_mono ha hb hab
    have := hu_gt a ha
    have : P.F P.sL / P.F (P.sRof b) < P.F P.sL / P.F (P.sRof a) :=
      div_lt_div_of_pos_left hFsL (by linarith) (by assumption)
    linarith
  have hSM : StrictMonoOn P.lieGain (Ioc 0 1) := by
    intro a ha b hb hab
    unfold Primitives.lieGain
    have g1 := hgpos a ha
    have g2 := hgmono a ha b hb hab
    calc a * ((P.F (P.sRof a) - P.F P.sL) / P.F (P.sRof a))
        < b * ((P.F (P.sRof a) - P.F P.sL) / P.F (P.sRof a)) := by
          exact mul_lt_mul_of_pos_right hab g1
      _ < b * ((P.F (P.sRof b) - P.F P.sL) / P.F (P.sRof b)) :=
          mul_lt_mul_of_pos_left g2 (lt_trans ha.1 hab)
  have hC : ContinuousOn P.lieGain (Ioc 0 1) := by
    have hFc : ContinuousOn P.F (Icc 0 1) := hFC.continuousOn
    have hu : ContinuousOn (fun b => P.F (P.sRof b)) (Ioc 0 1) :=
      (hFc.comp hcont (fun b hb => hrangeI b hb)).mono Ioc_subset_Icc_self
    unfold Primitives.lieGain
    apply ContinuousOn.mul continuousOn_id
    apply ContinuousOn.div (hu.sub continuousOn_const) hu
    intro b hb
    linarith [hu_gt b hb]
  have hB : P.lieGain 1 = P.Bbar := by
    unfold Primitives.lieGain Primitives.Bbar; rw [h1]; ring
  have hle : ∀ b ∈ Ioc (0:ℝ) 1, P.lieGain b ≤ b := by
    intro b hb
    unfold Primitives.lieGain
    have := hgle b hb
    nlinarith [hb.1]
  refine ⟨hSM, hC, hB, ?_⟩
  intro ℓ hℓ hℓB
  have hB1 : P.Bbar ≤ 1 := by rw [← hB]; simpa using hle 1 ⟨zero_lt_one, le_rfl⟩
  have hδ : ℓ / 2 ∈ Ioc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hδv : P.lieGain (ℓ / 2) < ℓ := by linarith [hle _ hδ]
  have hsub : Icc (ℓ / 2) 1 ⊆ Ioc (0:ℝ) 1 := fun x hx => ⟨by linarith [hx.1], hx.2⟩
  obtain ⟨b, hb, hbv⟩ := intermediate_value_Icc (by linarith : ℓ / 2 ≤ 1) (hC.mono hsub)
    ⟨hδv.le, by rw [hB]; exact hℓB.le⟩
  have hb1 : b ≠ 1 := by rintro rfl; rw [hB] at hbv; linarith
  refine ⟨b, ⟨⟨by linarith [hb.1], lt_of_le_of_ne hb.2 hb1⟩, hbv⟩, ?_⟩
  rintro c ⟨hc, hcv⟩
  exact hSM.injOn ⟨hc.1, hc.2.le⟩ (hsub hb) (hcv.trans hbv.symm)
