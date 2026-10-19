-- Prove2me | solution 1 for QuantumMC.MeanEst.lemma_4_band_bound
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T18:08:50.679429+00:00
-- url     : https://prove2.me/submissions/e91b72bd-e333-4992-a0e7-f994dfe81b4a

import Mathlib
import Definitions.Def_QuantumMC_MeanEst_Setting

open MeasureTheory ProbabilityTheory Filter
set_option linter.unusedVariables false

open QuantumMC.MeanEst

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : MemLp X 2 P)
    (hpos : ∀ ω, 0 ≤ X ω) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (∫ ω, truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X ω ∂P) ≤
      l2norm P (truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X) ^ 2 /
        (2 : ℝ) ^ (ℓ - 1) := by
  set c : ℝ := (2 : ℝ) ^ (ℓ - 1) with hcdef
  set d : ℝ := (2 : ℝ) ^ ℓ with hddef
  set A : Ω → ℝ := truncIco c d X with hAdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hAle : ∀ ω, 0 ≤ A ω := fun ω => by
    rw [hAdef]; simp only [truncIco]; split
    · exact hpos ω
    · exact le_refl 0
  have hAX : ∀ ω, A ω ≤ X ω := fun ω => by
    rw [hAdef]; simp only [truncIco]; split
    · exact le_refl _
    · exact hpos ω
  have hAesm : AEStronglyMeasurable A P := by
    have hXa : AEMeasurable X P := hX.aestronglyMeasurable.aemeasurable
    refine (show AEMeasurable A P from
      ⟨truncIco c d (hXa.mk X), ?_, ?_⟩).aestronglyMeasurable
    · unfold truncIco
      exact Measurable.ite
        ((measurableSet_le measurable_const hXa.measurable_mk).inter
          (measurableSet_lt hXa.measurable_mk measurable_const))
        hXa.measurable_mk measurable_const
    · rw [hAdef]
      filter_upwards [hXa.ae_eq_mk] with ω hω
      simp only [truncIco, hω]
  have hA2int : Integrable (fun ω => A ω ^ 2) P := by
    refine Integrable.mono' (hX.integrable_sq) ?_ ?_
    · convert hAesm.mul hAesm using 1
      ext ω; simp [pow_two]
    · exact Eventually.of_forall (fun ω => by
        rw [Real.norm_of_nonneg (sq_nonneg (A ω))]
        nlinarith [hAle ω, hAX ω, hpos ω])
  have hsq : l2norm P A ^ 2 = ∫ ω, A ω ^ 2 ∂P := by
    rw [l2norm, Real.sq_sqrt (integral_nonneg (fun ω => sq_nonneg (A ω)))]
  rw [hsq]
  have hgint : Integrable (fun ω => A ω ^ 2 / c) P := hA2int.div_const c
  have hpt : ∀ ω, A ω ≤ A ω ^ 2 / c := by
    intro ω
    rw [le_div_iff₀ hcpos]
    by_cases h : c ≤ X ω ∧ X ω < d
    · have hAeq : A ω = X ω := by rw [hAdef]; simp only [truncIco]; rw [if_pos h]
      rw [hAeq]; nlinarith [h.1, hpos ω]
    · have hA0 : A ω = 0 := by rw [hAdef]; simp only [truncIco]; rw [if_neg h]
      rw [hA0]; simp
  calc (∫ ω, A ω ∂P) ≤ ∫ ω, A ω ^ 2 / c ∂P :=
        integral_mono_of_nonneg (f := A) (g := fun ω => A ω ^ 2 / c)
          (Eventually.of_forall hAle) hgint (Eventually.of_forall hpt)
    _ = (∫ ω, A ω ^ 2 ∂P) / c := by rw [integral_div]
