-- Prove2me | solution 2 for QiFixedDesign.Concentration.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-13T19:08:59.068907+00:00
-- url     : https://prove2.me/submissions/825504b9-8873-4bfb-b42b-9a0d2575934e

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

private def clip (n : ℕ) (u : ℝ) : ℝ := max (-(n : ℝ)) (min (n : ℝ) u)

private lemma clip_lipschitz (n : ℕ) : LipschitzWith 1 (clip n) := by
  exact (LipschitzWith.id.const_min (n : ℝ)).const_max (-(n : ℝ))

private lemma clip_abs_le (n : ℕ) (u : ℝ) : |clip n u| ≤ n := by
  exact abs_le.mpr ⟨le_max_left _ _, max_le (neg_le_self (Nat.cast_nonneg n)) (min_le_left _ _)⟩

private lemma clip_integrable {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (g : α → ℝ) (hg : Measurable g) (n : ℕ) :
    Integrable (fun u => clip n (g u)) μ := by
  exact Integrable.of_bound ((clip_lipschitz n).continuous.measurable.comp hg).aestronglyMeasurable
    (n : ℝ) (ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using clip_abs_le n (g u))

private lemma clip_coupling_bound (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    (π : Measure (ℝ × ℝ)) (hπ : π.map Prod.fst = μ ∧ π.map Prod.snd = ν) (n : ℕ) :
    ENNReal.ofReal |(∫ u, clip n u ∂ν) - ∫ u, clip n u ∂μ| ≤
      ∫⁻ x : ℝ × ℝ, ENNReal.ofReal |x.1 - x.2| ∂π := by
  have hp : IsProbabilityMeasure π := ⟨by
    have hh := congrArg (fun ρ : Measure ℝ => ρ Set.univ) hπ.1
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ,
      measure_univ] using hh⟩
  let _ := hp
  rw [← hπ.2, ← hπ.1,
    integral_map_of_stronglyMeasurable measurable_snd (clip_lipschitz n).continuous.stronglyMeasurable,
    integral_map_of_stronglyMeasurable measurable_fst (clip_lipschitz n).continuous.stronglyMeasurable]
  rw [← integral_sub (clip_integrable π Prod.snd measurable_snd n)
    (clip_integrable π Prod.fst measurable_fst n)]
  refine le_trans (b := ∫⁻ x : ℝ × ℝ, ENNReal.ofReal |clip n x.2 - clip n x.1| ∂π) ?_ ?_
  · simpa only [Real.enorm_eq_ofReal_abs] using
      enorm_integral_le_lintegral_enorm (fun x : ℝ × ℝ => clip n x.2 - clip n x.1)
  · exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal
      (by simpa only [Real.dist_eq, NNReal.coe_one, one_mul, abs_sub_comm] using
        (clip_lipschitz n).dist_le_mul x.2 x.1)

private lemma clip_tendsto (u : ℝ) : Tendsto (fun n : ℕ => clip n u) atTop (𝓝 u) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop |u|] with n hn
  simp only [clip, min_eq_right (abs_le.mp hn).2, max_eq_right (abs_le.mp hn).1]

private lemma clip_shift_tendsto (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    Tendsto (fun n : ℕ => ∫ u, clip n (u + t) - clip n u ∂μ) atTop (𝓝 t) := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n u => clip n (u + t) - clip n u) (f := fun _ => t)
    (fun _ => |t|) (fun n => ?_) (integrable_const |t|) (fun n => ?_) ?_
  · simpa using h
  · exact (((clip_lipschitz n).continuous.comp (continuous_id.add continuous_const)).sub
      (clip_lipschitz n).continuous).aestronglyMeasurable
  · exact ae_of_all _ fun u => by
      simpa only [Real.norm_eq_abs, Real.dist_eq, NNReal.coe_one, one_mul,
        add_sub_cancel_left] using (clip_lipschitz n).dist_le_mul (u + t) u
  · exact ae_of_all _ fun u => by
      simpa only [add_sub_cancel_left] using (clip_tendsto (u + t)).sub (clip_tendsto u)

private lemma shift_cost_lower (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ)
    (π : Measure (ℝ × ℝ))
    (hπ : π.map Prod.fst = μ ∧ π.map Prod.snd = μ.map (fun u => u + t)) :
    ENNReal.ofReal |t| ≤ ∫⁻ x : ℝ × ℝ, ENNReal.ofReal |x.1 - x.2| ∂π := by
  have hlim : Tendsto (fun n : ℕ =>
      ENNReal.ofReal |∫ u, clip n (u + t) - clip n u ∂μ|) atTop (𝓝 (ENNReal.ofReal |t|)) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (clip_shift_tendsto μ t).abs
  apply le_of_tendsto' hlim
  intro n
  have hb := clip_coupling_bound μ (μ.map (fun u => u + t)) π hπ n
  rw [integral_map_of_stronglyMeasurable (μ := μ) (φ := fun u : ℝ => u + t)
    (measurable_id.add_const t)
    (clip_lipschitz n).continuous.stronglyMeasurable,
    ← integral_sub (clip_integrable μ (fun u => u + t) (measurable_id.add_const t) n)
      (clip_integrable μ (fun u : ℝ => u) measurable_id n)] at hb
  exact hb

private lemma inf_shift_cost (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    (⨅ (π : Measure (ℝ × ℝ))
      (_ : π.map Prod.fst = μ ∧ π.map Prod.snd = μ.map (fun u => u + t)),
      ∫⁻ x : ℝ × ℝ, ENNReal.ofReal |x.1 - x.2| ∂π) = ENNReal.ofReal |t| := by
  refine le_antisymm ?_ (le_iInf fun π => le_iInf fun hπ => shift_cost_lower μ t π hπ)
  let π : Measure (ℝ × ℝ) := μ.map (fun u : ℝ => (u, u + t))
  have hm : Measurable (fun u : ℝ => (u, u + t)) :=
    measurable_id.prodMk (measurable_id.add_const t)
  have hπ : π.map Prod.fst = μ ∧ π.map Prod.snd = μ.map (fun u => u + t) := by
    simp only [π, Measure.map_map measurable_fst hm, Measure.map_map measurable_snd hm,
      Function.comp_def, Measure.map_id', and_true]
  refine iInf_le_of_le π (iInf_le_of_le hπ ?_)
  have hc : Measurable (fun x : ℝ × ℝ => ENNReal.ofReal |x.1 - x.2|) :=
    (ENNReal.continuous_ofReal.comp (continuous_fst.sub continuous_snd).abs).measurable
  simp [π, lintegral_map hc hm]


theorem solution (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t : ℝ) (hν : ν = μ.map (fun u => u + t)) :
    WassersteinDRO.Duality.wassersteinDistance 1 μ ν = ENNReal.ofReal |t| := by
  simpa [WassersteinDRO.Duality.wassersteinDistance, hν, Real.norm_eq_abs] using inf_shift_cost μ t
