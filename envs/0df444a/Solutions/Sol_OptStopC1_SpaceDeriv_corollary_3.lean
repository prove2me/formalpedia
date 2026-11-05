-- Prove2me | solution 1 for OptStopC1.SpaceDeriv.corollary_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T02:56:06.083977+00:00
-- url     : https://prove2.me/submissions/50e5ac8b-6669-4d99-b915-05feecbffb45

import Theorems.Thm_OptStopC1_SpaceDeriv_corollary_2

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
    (hPR : IsProbRegular X P D z) (hF : IsStrongFeller X P)
    (xs : ℕ → State d) (hxs : ∀ n, xs n ∈ Dᶜ)
    (hconv : Tendsto xs atTop (𝓝 z))
    (ε : ℝ≥0) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | (ε : ℝ≥0∞) ≤ entryTime X (xs n) D ω})
      atTop (𝓝 0) := by
  have hG := OptStopC1.SpaceDeriv.corollary_2 hd P 𝔽 X hX D hD z hz hPR hF ε hε
  exact hG.comp (tendsto_nhdsWithin_iff.2 ⟨hconv, Eventually.of_forall hxs⟩)
