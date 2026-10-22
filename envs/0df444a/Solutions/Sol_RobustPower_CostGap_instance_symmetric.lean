-- Prove2me | solution 1 for RobustPower.CostGap.instance_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:21:55.888558+00:00
-- url     : https://prove2.me/submissions/5264b00f-e9dd-454d-af7d-81ee9819319c

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets

open MeasureTheory


namespace RobustPower.CostGap

instance g25s_prob_Icc : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩

theorem instance_symmetric_core {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Ω → Fin n → ℝ) (hd : Measurable d) (hrange : Set.range d = Set.Icc 0 1)
    (hlaw : μ.map d = Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))) :
    RobustPower.StochGap.IsSymmetricAbout (Set.range fun ω => ((fun _ => 1 : Fin 1 → ℝ), d ω))
        ((fun _ => 1 : Fin 1 → ℝ), (fun _ => 1 / 2 : Fin n → ℝ)) ∧
      ∫ ω, d ω ∂μ = (fun _ => 1 / 2 : Fin n → ℝ) := by
  have hmem : ∀ p : (Fin 1 → ℝ) × (Fin n → ℝ),
      p ∈ (Set.range fun ω => ((fun _ => 1 : Fin 1 → ℝ), d ω)) ↔
        (∀ i, p.1 i = 1) ∧ ∀ j, 0 ≤ p.2 j ∧ p.2 j ≤ 1 := by
    intro p
    constructor
    · rintro ⟨ω, rfl⟩
      have h : d ω ∈ Set.Icc (0 : Fin n → ℝ) 1 := hrange ▸ Set.mem_range_self ω
      exact ⟨fun _ => rfl, fun j => ⟨h.1 j, h.2 j⟩⟩
    · rintro ⟨h1, h2⟩
      have : p.2 ∈ Set.range d := by
        rw [hrange]; exact ⟨fun j => (h2 j).1, fun j => (h2 j).2⟩
      obtain ⟨ω, hω⟩ := this
      refine ⟨ω, ?_⟩
      ext i
      · simp [h1 i]
      · simp [hω]
  have hdj_bd : ∀ ω j, 0 ≤ d ω j ∧ d ω j ≤ 1 := by
    intro ω j
    have h : d ω ∈ Set.Icc (0 : Fin n → ℝ) 1 := hrange ▸ Set.mem_range_self ω
    exact ⟨h.1 j, h.2 j⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hmem]
    refine ⟨fun _ => rfl, fun j => ⟨by norm_num, by norm_num⟩⟩
  · intro z
    rw [hmem, hmem]
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Pi.add_apply,
      Pi.sub_apply]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => by linarith [h1 i], fun j => ⟨by linarith [(h2 j).2], by linarith [(h2 j).1]⟩⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => by linarith [h1 i], fun j => ⟨by linarith [(h2 j).2], by linarith [(h2 j).1]⟩⟩
  · have hdj : ∀ j, Measurable (fun ω => d ω j) := fun j => (measurable_pi_apply j).comp hd
    have hint : ∀ j, Integrable (fun ω => d ω j) μ := by
      intro j
      refine Integrable.of_bound (hdj j).aestronglyMeasurable 1 (Filter.Eventually.of_forall ?_)
      intro ω
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [(hdj_bd ω j).1], (hdj_bd ω j).2⟩
    funext j
    rw [eval_integral hint j]
    have h1 := integral_map (μ := μ) hd.aemeasurable
      (f := fun x : Fin n → ℝ => x j) (measurable_pi_apply j).aestronglyMeasurable
    rw [hlaw] at h1
    rw [← h1]
    have hmp := measurePreserving_eval (μ := fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)) j
    have h2 := integral_map (μ := Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)))
      (measurable_pi_apply j).aemeasurable (f := fun t : ℝ => t) measurable_id.aestronglyMeasurable
    rw [hmp.map_eq] at h2
    rw [← h2, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    simp

end RobustPower.CostGap

open RobustPower.CostGap


theorem solution {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Ω → Fin n → ℝ) (hd : Measurable d) (hrange : Set.range d = Set.Icc 0 1)
    (hlaw : μ.map d = Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))) :
    RobustPower.StochGap.IsSymmetricAbout (Set.range fun ω => ((fun _ => 1 : Fin 1 → ℝ), d ω))
        ((fun _ => 1 : Fin 1 → ℝ), (fun _ => 1 / 2 : Fin n → ℝ)) ∧
      ∫ ω, d ω ∂μ = (fun _ => 1 / 2 : Fin n → ℝ) := by
  exact instance_symmetric_core hn μ d hd hrange hlaw
