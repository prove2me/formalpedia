-- Prove2me | solution 1 for OptStopC1.SpaceDeriv.corollary_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T02:56:05.298086+00:00
-- url     : https://prove2.me/submissions/9b07f6f1-e83f-49fe-9b9f-96dc624b6425

import Theorems.Thm_OptStopC1_SpaceDeriv_lemma_1

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Interval

open OptStopC1.SpaceDeriv in
theorem solution
    {d : ℕ} (hd : 0 < d) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (X : Flow d Ω)
    (hX : IsStandardMarkovFlow X P 𝔽)
    (D : Set (State d)) (hD : IsClosed D)
    (z : State d) (hz : z ∈ frontier Dᶜ)
    (hPR : IsProbRegular X P D z) (hF : IsStrongFeller X P) :
    IsGreenRegular X P Dᶜ D z := by
  intro ε hε
  have husc := OptStopC1.SpaceDeriv.lemma_1 hd P 𝔽 X hX D hD hF ε hε
  -- the delayed hitting probability vanishes at z
  have hmeas : MeasurableSet {ω | hittingTime X z D ω = 0} := by
    have hst := (hX.2.2.2.2.2.2.1 D (Or.inr hD) z).2.1
    have h0 := 𝔽.le 0 _ (hst 0)
    have hset : {ω | hittingTime X z D ω = 0} =
        {ω | hittingTime X z D ω ≤ ((0 : ℝ≥0) : ℝ≥0∞)} := by
      ext ω
      simp
    rw [hset]
    exact h0
  have hz0 : P {ω | (ε : ℝ≥0∞) ≤ hittingTime X z D ω} = 0 := by
    have hc : P {ω | hittingTime X z D ω = 0}ᶜ = 0 := by
      rw [prob_compl_eq_zero_iff hmeas]; exact hPR
    refine measure_mono_null (fun ω hω => ?_) hc
    simp only [mem_ofPred_eq, mem_compl_iff] at hω ⊢
    intro h0
    rw [h0] at hω
    have h1 := le_antisymm hω zero_le
    simp at h1
    exact hε.ne' h1
  have hle : ∀ x ω, entryTime X x D ω ≤ hittingTime X x D ω := by
    intro x ω
    apply sInf_le_sInf
    exact image_mono fun t ht => ht.2
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hev := husc z δ (by show P {ω | (ε : ℝ≥0∞) ≤ hittingTime X z D ω} < δ; rw [hz0]; exact hδ)
  have hev' : ∀ᶠ x in 𝓝[Dᶜ] z, P {ω | (ε : ℝ≥0∞) ≤ hittingTime X x D ω} < δ :=
    nhdsWithin_le_nhds hev
  filter_upwards [hev'] with x hx
  refine le_trans (measure_mono fun ω hω => ?_) hx.le
  exact le_trans hω (hle x ω)
