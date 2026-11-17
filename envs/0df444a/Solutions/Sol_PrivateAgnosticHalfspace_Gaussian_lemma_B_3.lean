-- Prove2me | solution 1 for PrivateAgnosticHalfspace.Gaussian.lemma_B_3
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-16T11:01:52.704875+00:00
-- url     : https://prove2.me/submissions/c1e7f0c2-5754-41a0-8080-9ea9b8cfdff7

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
open MeasureTheory ProbabilityTheory

set_option autoImplicit false

lemma integral_le_of_event_bound {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c δ : ℝ) (g : α → ℝ) (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    (hsets : ∀ s, MeasurableSet s → μ.real s ≤ c * ν.real s + δ) :
    ∫ x, g x ∂μ ≤ c * ∫ x, g x ∂ν + δ := by
  let A : ℝ → ℝ := fun t => μ.real {x | t ≤ g x}
  let B : ℝ → ℝ := fun t => ν.real {x | t ≤ g x}
  have hset : MeasurableSet {p : ℝ × α | p.1 ≤ g p.2} :=
    measurableSet_le measurable_fst (hg.comp measurable_snd)
  have hAmeas : Measurable A := by
    change Measurable (fun t => (μ {x | t ≤ g x}).toReal)
    exact (measurable_measure_prodMk_left_finite hset).ennreal_toReal
  have hBmeas : Measurable B := by
    change Measurable (fun t => (ν {x | t ≤ g x}).toReal)
    exact (measurable_measure_prodMk_left_finite hset).ennreal_toReal
  have hAint : Integrable A (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    apply Measure.integrableOn_of_bounded (μ := volume) (s := Set.Ioc (0 : ℝ) 1) (M := 1)
    · simp
    · exact hAmeas.aestronglyMeasurable
    · filter_upwards [] with t
      have hmeasure : μ.real {x | t ≤ g x} ≤ 1 := by
        rw [Measure.real_def]
        have hμset : μ {x | t ≤ g x} ≤ 1 := by
          calc
            μ {x | t ≤ g x} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := by simp
        exact ENNReal.toReal_mono (by simp) hμset
      have hnonneg : 0 ≤ A t := by simp [A, Measure.real_def]
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith, hmeasure⟩
  have hBint : Integrable B (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    apply Measure.integrableOn_of_bounded (μ := volume) (s := Set.Ioc (0 : ℝ) 1) (M := 1)
    · simp
    · exact hBmeas.aestronglyMeasurable
    · filter_upwards [] with t
      have hmeasure : ν.real {x | t ≤ g x} ≤ 1 := by
        rw [Measure.real_def]
        have hνset : ν {x | t ≤ g x} ≤ 1 := by
          calc
            ν {x | t ≤ g x} ≤ ν Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := by simp
        exact ENNReal.toReal_mono (by simp) hνset
      have hnonneg : 0 ≤ B t := by simp [B, Measure.real_def]
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith, hmeasure⟩
  have hgint (ρ : Measure α) [IsProbabilityMeasure ρ] : Integrable g ρ := by
    have hconst : Integrable (fun _ : α => (1 : ℝ)) ρ := integrable_const _
    apply hconst.mono' hg.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hg0 x], hg1 x⟩
  have hμlayer := (hgint μ).integral_eq_integral_Ioc_meas_le (ae_of_all _ (fun x => hg0 x))
    (ae_of_all _ (fun x => hg1 x))
  have hνlayer := (hgint ν).integral_eq_integral_Ioc_meas_le (ae_of_all _ (fun x => hg0 x))
    (ae_of_all _ (fun x => hg1 x))
  have hscaled : Integrable (fun t => c * B t) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    hBint.const_mul c
  have hconst : Integrable (fun _ : ℝ => δ) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := integrable_const _
  have hsum : Integrable (fun t => c * B t + δ) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    hscaled.add hconst
  have hle : A ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] (fun t => c * B t + δ) := by
    filter_upwards [] with t
    change μ.real {x | t ≤ g x} ≤ c * ν.real {x | t ≤ g x} + δ
    exact hsets {x | t ≤ g x} (measurableSet_le measurable_const hg)
  calc
    ∫ x, g x ∂μ = ∫ t in Set.Ioc (0 : ℝ) 1, A t := by simpa [A] using hμlayer
    _ ≤ ∫ t in Set.Ioc (0 : ℝ) 1, c * B t + δ := integral_mono_ae hAint hsum hle
    _ = c * (∫ t in Set.Ioc (0 : ℝ) 1, B t) + δ := by
      rw [integral_add hscaled hconst, integral_const_mul]
      simp [integral_const, Real.volume_Ioc]
    _ = c * (∫ x, g x ∂ν) + δ := by simpa [B] using congrArg (fun z : ℝ => c * z + δ) hνlayer.symm


open scoped ENNReal

theorem solution {X Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (n : ℕ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 ≤ δ ∧ δ < 1)
    (M : PrivateUniformGen.Characterization.Mechanism X Y n)
    (hM : PrivateUniformGen.Characterization.IsDP M ε δ)
    (f : Kernel Y Z) [IsMarkovKernel f] :
    ∃ A : PrivateUniformGen.Characterization.Mechanism X Z n,
      (∀ S, (A S : Measure Z) = f ∘ₘ (M S : Measure Y)) ∧
      PrivateUniformGen.Characterization.IsDP A ε δ := by
  let A : PrivateUniformGen.Characterization.Mechanism X Z n :=
    fun S => ⟨f ∘ₘ (M S : Measure Y), by infer_instance⟩
  refine ⟨A, ?_, ?_⟩
  · intro S
    rfl
  · intro S S' hSS O hO
    let g : Y → ℝ := fun y => (f y).real O
    have hg : Measurable g := by
      change Measurable (fun y => ((f y) O).toReal)
      exact (f.measurable_coe hO).ennreal_toReal
    have hg0 : ∀ y, 0 ≤ g y := by
      intro y
      simp [g, Measure.real_def]
    have hg1 : ∀ y, g y ≤ 1 := by
      intro y
      have hmeasure : (f y) O ≤ 1 := by
        calc
          (f y) O ≤ (f y) Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := by simp
      have hreal : ((f y) O).toReal ≤ 1 := ENNReal.toReal_mono (by simp) hmeasure
      simpa [g, Measure.real_def] using hreal
    have hsets : ∀ s, MeasurableSet s →
        (M S : Measure Y).real s ≤ Real.exp ε * (M S' : Measure Y).real s + δ := by
      intro s hs
      exact hM S S' hSS s hs
    have hi := integral_le_of_event_bound (M S : Measure Y) (M S' : Measure Y)
      (Real.exp ε) δ g hg hg0 hg1 hsets
    have hconv : ∀ y, ENNReal.ofReal (g y) = (f y) O := by
      intro y
      simp [g, Measure.real_def, ENNReal.ofReal_toReal, measure_ne_top]
    have hgint (T : Fin n → X) : Integrable g (M T : Measure Y) := by
      have hconst : Integrable (fun _ : Y => (1 : ℝ)) (M T : Measure Y) := integrable_const _
      apply hconst.mono' hg.aestronglyMeasurable
      filter_upwards [] with y
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hg0 y], hg1 y⟩
    have hgnonneg (T : Fin n → X) : 0 ≤ᵐ[(M T : Measure Y)] g := ae_of_all _ hg0
    have hreal (T : Fin n → X) :
        (A T : Measure Z).real O = ∫ y, g y ∂(M T : Measure Y) := by
      rw [Measure.real_def, show (A T : Measure Z) = f ∘ₘ (M T : Measure Y) by rfl,
        Measure.bind_apply hO f.aemeasurable]
      calc
        (∫⁻ y, (f y) O ∂(M T : Measure Y)).toReal =
            (∫⁻ y, ENNReal.ofReal (g y) ∂(M T : Measure Y)).toReal := by
              congr 1
              apply lintegral_congr
              exact fun y => (hconv y).symm
        _ = (ENNReal.ofReal (∫ y, g y ∂(M T : Measure Y))).toReal := by
              rw [← ofReal_integral_eq_lintegral_ofReal (hgint T) (hgnonneg T)]
        _ = ∫ y, g y ∂(M T : Measure Y) := by
              rw [ENNReal.toReal_ofReal]
              exact integral_nonneg_of_ae (hgnonneg T)
    rw [hreal S, hreal S']
    exact hi

