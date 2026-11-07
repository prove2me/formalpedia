-- Prove2me | solution 1 for SampleMechDesign.theorem_3_9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T16:45:23.070873+00:00
-- url     : https://prove2.me/submissions/bc3932c5-a53a-4df4-bffa-ddee5f7458f5

import Mathlib
import Definitions.Def_BartlettBousquetMendelson_LocalRad_IsPointwiseMeasurableClass
import Definitions.Def_SampleMechDesign_IsDelineable
import Theorems.Thm_SampleMechDesign_theorem_3_8
import Theorems.Thm_SampleMechDesign_lemma_3_10

open MeasureTheory

open SampleMechDesign BartlettBousquetMendelson.LocalRad in
theorem solution {X : Type*} [MeasurableSpace X] {d t : ℕ} (hd : 1 ≤ d) (ht : 1 ≤ t)
    {P : Set (Fin d → ℝ)} {profit : (Fin d → ℝ) → X → ℝ} (hdel : IsDelineable d t P profit)
    (hmeas : ∀ p ∈ P, Measurable (profit p)) (hpm : IsPointwiseMeasurableClass (profit '' P))
    (D : Measure X) [IsProbabilityMeasure D] {U : ℝ}
    (hU : ∀ᵐ v ∂D, ∀ p ∈ P, profit p v ∈ Set.Icc 0 U)
    {N : ℕ} (hN : 1 ≤ N) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Measure.pi (fun _ : Fin N => D)
      {S : Fin N → X | ∃ p ∈ P,
        120 * U * √(9 * (d : ℝ) * Real.log (4 * (d : ℝ) * (t : ℝ)) / (N : ℝ)) +
            4 * U * √(2 * Real.log (4 / δ) / (N : ℝ)) <
          |(1 / (N : ℝ)) * ∑ i, profit p (S i) - ∫ v, profit p v ∂D|} <
      ENNReal.ofReal δ := by
  have hF : ∀ f ∈ profit '' P, Measurable f := by
    rintro f ⟨p, hp, rfl⟩
    exact hmeas p hp
  have hk : ∀ (m : ℕ) (z : Fin m → X), FoundationsML.Regression.Shatters (profit '' P) z →
      (m : ℝ) ≤ 9 * (d : ℝ) * Real.log (4 * (d : ℝ) * (t : ℝ)) := by
    intro m z hz
    exact SampleMechDesign.lemma_3_10 hd ht hdel z hz
  have hU' : ∀ᵐ v ∂D, ∀ f ∈ profit '' P, f v ∈ Set.Icc 0 U := by
    filter_upwards [hU] with v hv
    rintro f ⟨p, hp, rfl⟩
    exact hv p hp
  have h38 := SampleMechDesign.theorem_3_8 hF hpm hk D hU' hN hδ0 hδ1
  refine lt_of_le_of_lt (measure_mono ?_) h38
  rintro S ⟨p, hp, hlt⟩
  exact ⟨profit p, ⟨p, hp, rfl⟩, hlt⟩
