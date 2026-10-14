-- Prove2me | solution 1 for PersistClust.Count.theorem_4_8_s2_tau_null
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T15:11:32.367988+00:00
-- url     : https://prove2.me/submissions/2ac2f01e-817a-47d0-abae-ddd1de14ec6f

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_Algorithm

open MeasureTheory Bundle
open scoped ContDiff Manifold ENNReal

open PersistClust.Count

theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) (n : ℕ)
    (τ : ℝ) (hdens : IsDensity μ f) (hf : Measurable f) (hτnull : μ {x : X | f x = τ} = 0) :
    sampleMeasure μ n f {pts : Fin n → X | ∃ i : Fin n, f (pts i) = τ} = 0 := by
  obtain ⟨hnonneg, hintegrable, hint⟩ := hdens
  have hA : MeasurableSet {x : X | f x = τ} := (MeasurableSet.singleton τ).preimage hf
  -- each one-coordinate slice is null for the single-sample law: the S1 machinery with the
  -- vanishing-integral step replaced by the restricted-const step `ofReal τ * μ A = 0`
  have h0 : sampleLaw μ f {x : X | f x = τ} = 0 := by
    show μ.withDensity (fun x => ENNReal.ofReal (f x)) {x : X | f x = τ} = 0
    have h1 : μ.withDensity (fun x => ENNReal.ofReal (f x)) {x : X | f x = τ}
        = ∫⁻ a in {x : X | f x = τ}, ENNReal.ofReal (f a) ∂μ :=
      withDensity_apply _ hA
    have h2 : ∫⁻ a in {x : X | f x = τ}, ENNReal.ofReal (f a) ∂μ = 0 := by
      rw [← lintegral_indicator hA]
      -- on the level set the integrand is the constant `ofReal τ`
      have hpt : ∀ a : X, {x : X | f x = τ}.indicator (fun x => ENNReal.ofReal (f x)) a
          = {x : X | f x = τ}.indicator (fun _ => ENNReal.ofReal τ) a := by
        intro a
        by_cases ha : a ∈ {x : X | f x = τ}
        · have hfa : f a = τ := ha
          rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha, hfa]
        · rw [Set.indicator_of_notMem ha (fun x => ENNReal.ofReal (f x)),
            Set.indicator_of_notMem ha (fun _ => ENNReal.ofReal τ)]
      rw [lintegral_congr hpt, lintegral_indicator hA, setLIntegral_const, hτnull, mul_zero]
    rw [h1, h2]
  -- steps 2–5 of the S1 template, verbatim
  have hνuniv : sampleLaw μ f Set.univ = 1 := by
    show μ.withDensity (fun x => ENNReal.ofReal (f x)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hintegrable (ae_of_all μ hnonneg), hint]
    exact ENNReal.ofReal_one
  haveI : IsProbabilityMeasure (sampleLaw μ f) := ⟨hνuniv⟩
  have key : ∀ i : Fin n,
      sampleMeasure μ n f {pts : Fin n → X | f (pts i) = τ} = 0 := fun i =>
    Measure.pi_eval_preimage_null (μ := fun _ : Fin n => sampleLaw μ f) h0
  have hU : {pts : Fin n → X | ∃ i : Fin n, f (pts i) = τ}
      = ⋃ i : Fin n, {pts : Fin n → X | f (pts i) = τ} := by
    ext pts
    simp
  rw [hU]
  exact measure_iUnion_null_iff (μ := sampleMeasure μ n f) |>.2 key
