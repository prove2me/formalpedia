-- Prove2me | solution 1 for OptStopC1.SpaceDeriv.corollary_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T02:56:06.855861+00:00
-- url     : https://prove2.me/submissions/03ea5670-3a07-4a7d-8bd6-ffee70c47d84

import Theorems.Thm_OptStopC1_SpaceDeriv_lemma_4

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
    (hPR : IsProbRegular X P (interior D) z)
    (hcont : FlowContinuousAE X P) :
    IsGreenRegular X P Dᶜ (interior D) z ∧
    IsGreenRegular X P Dᶜ D z := by
  have hint : IsGreenRegular X P Dᶜ (interior D) z := by
    intro ε hε
    have husc := OptStopC1.SpaceDeriv.lemma_4 hd P 𝔽 X hX D hD hcont ε hε
    have hmeas : MeasurableSet {ω | hittingTime X z (interior D) ω = 0} := by
      have hst := (hX.2.2.2.2.2.2.1 (interior D) (Or.inl isOpen_interior) z).2.1
      have h0 := 𝔽.le 0 _ (hst 0)
      have hset : {ω | hittingTime X z (interior D) ω = 0} =
          {ω | hittingTime X z (interior D) ω ≤ ((0 : ℝ≥0) : ℝ≥0∞)} := by
        ext ω
        simp
      rw [hset]
      exact h0
    have hz0 : P {ω | (ε : ℝ≥0∞) ≤ hittingTime X z (interior D) ω} = 0 := by
      have hc : P {ω | hittingTime X z (interior D) ω = 0}ᶜ = 0 := by
        rw [prob_compl_eq_zero_iff hmeas]; exact hPR
      refine measure_mono_null (fun ω hω => ?_) hc
      simp only [mem_ofPred_eq, mem_compl_iff] at hω ⊢
      intro h0
      rw [h0] at hω
      have h1 := le_antisymm hω zero_le
      simp at h1
      exact hε.ne' h1
    have hle : ∀ x ω, entryTime X x (interior D) ω ≤ hittingTime X x (interior D) ω := by
      intro x ω
      apply sInf_le_sInf
      exact image_mono fun t ht => ht.2
    rw [ENNReal.tendsto_nhds_zero]
    intro δ hδ
    have hev := husc z δ (by
      show P {ω | (ε : ℝ≥0∞) ≤ hittingTime X z (interior D) ω} < δ
      rw [hz0]; exact hδ)
    have hev' : ∀ᶠ x in 𝓝[Dᶜ] z,
        P {ω | (ε : ℝ≥0∞) ≤ hittingTime X x (interior D) ω} < δ :=
      nhdsWithin_le_nhds hev
    filter_upwards [hev'] with x hx
    refine le_trans (measure_mono fun ω hω => ?_) hx.le
    exact le_trans hω (hle x ω)
  refine ⟨hint, fun ε hε => ?_⟩
  -- entering D is no later than entering its interior
  have hmono : ∀ x ω, entryTime X x D ω ≤ entryTime X x (interior D) ω := by
    intro x ω
    apply sInf_le_sInf
    exact image_mono fun t (ht : X x t ω ∈ interior D) => (interior_subset ht : X x t ω ∈ D)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hint ε hε)
    (fun x => zero_le) (fun x => measure_mono fun ω hω => le_trans hω (hmono x ω))
