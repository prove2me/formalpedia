-- Prove2me | solution 1 for TeschlQM.Herglotz.ae_hasMeasureDeriv_top_singularPart
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:24:36.859798+00:00
-- url     : https://prove2.me/submissions/6a3472a5-8178-41a4-8ac3-ddb5ac8c9920

import Definitions.Def_TeschlQM_Herglotz_HasMeasureDeriv
import Definitions.Def_TeschlQM_Herglotz_scPart

open MeasureTheory Filter
open scoped ENNReal Topology
open TeschlQM.Herglotz

namespace TQ_9368

open Metric NNReal

lemma half_tendsto : Tendsto (fun ε : ℝ => ε / 2) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall (fun ε (h : 0 < ε) => (half_pos h : 0 < ε / 2))⟩
  have := ((continuous_id.div_const (2:ℝ)).tendsto (0:ℝ)).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  simpa using this

lemma bad_witness (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) (h : ¬ HasMeasureDeriv μ x ⊤) :
    ∃ n : ℕ, ∃ᶠ ε in 𝓝[>] (0:ℝ),
      μ (closedBall x (ε / 2)) ≤ ((2 * n : ℝ≥0) • volume) (closedBall x (ε / 2)) := by
  unfold HasMeasureDeriv at h
  rw [ENNReal.tendsto_nhds_top_iff_nat] at h
  push Not at h
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have hpos : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε := eventually_nhdsWithin_of_forall (fun ε h => h)
  refine (hn.and_eventually hpos).mono ?_
  rintro ε ⟨hle, hε⟩
  have hv0 : volume (ball x ε) ≠ 0 := by
    rw [Real.volume_ball]; simp; linarith
  have hvt : volume (ball x ε) ≠ ⊤ := by rw [Real.volume_ball]; exact ENNReal.ofReal_ne_top
  rw [ENNReal.div_le_iff hv0 hvt] at hle
  have hsub : closedBall x (ε / 2) ⊆ ball x ε := closedBall_subset_ball (by linarith)
  calc μ (closedBall x (ε / 2)) ≤ μ (ball x ε) := measure_mono hsub
    _ ≤ n * volume (ball x ε) := hle
    _ = ((2 * n : ℝ≥0) • volume) (closedBall x (ε / 2)) := by
      rw [Measure.smul_apply, Real.volume_ball, Real.volume_closedBall, ENNReal.smul_def,
        smul_eq_mul]
      rw [show 2 * ε = 2 * (2 * (ε / 2)) by ring, ENNReal.ofReal_mul (by norm_num)]
      push_cast
      rw [ENNReal.ofReal_ofNat]
      ring

end TQ_9368

open Metric NNReal in
theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ᵐ t ∂(μ.singularPart volume), HasMeasureDeriv μ t ⊤ := by
  have hms := Measure.mutuallySingular_singularPart μ volume
  set S := hms.nullSetᶜ with hS
  have hSvol : volume S = 0 := hms.measure_compl_nullSet
  have hSc : μ.singularPart volume Sᶜ = 0 := by rw [hS, compl_compl]; exact hms.measure_nullSet
  let s : ℕ → Set ℝ := fun n => {x | x ∈ S ∧ ∃ᶠ ε in 𝓝[>] (0:ℝ),
      μ (closedBall x (ε / 2)) ≤ ((2 * n : ℝ≥0) • volume) (closedBall x (ε / 2))}
  have hs : ∀ n, μ (s n) = 0 := by
    intro n
    let v := Besicovitch.vitaliFamily μ
    have hle : μ (s n) ≤ ((2 * n : ℝ≥0) • volume) (s n) := by
      refine v.measure_le_of_frequently_le (ρ := μ) _ (Measure.AbsolutelyContinuous.refl _) _ ?_
      intro x hx
      have ht := (Besicovitch.tendsto_filterAt μ x).comp TQ_9368.half_tendsto
      exact ht.frequently hx.2
    have h0 : ((2 * n : ℝ≥0) • volume) (s n) = 0 := by
      rw [Measure.smul_apply, measure_mono_null (fun x hx => hx.1) hSvol, smul_zero]
    exact le_antisymm (hle.trans h0.le) bot_le
  rw [ae_iff]
  refine measure_mono_null (t := (⋃ n, s n) ∪ Sᶜ) ?_ (measure_union_null ?_ hSc)
  · intro x hx
    by_cases hxS : x ∈ S
    · obtain ⟨n, hn⟩ := TQ_9368.bad_witness μ x hx
      exact Or.inl (Set.mem_iUnion.2 ⟨n, hxS, hn⟩)
    · exact Or.inr hxS
  · refine measure_iUnion_null fun n => ?_
    exact le_antisymm ((Measure.singularPart_le μ volume _).trans (hs n).le) bot_le
