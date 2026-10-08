-- Prove2me | solution 1 for TeschlQM.Herglotz.deriv_le_boundary_im
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T21:12:08.052991+00:00
-- url     : https://prove2.me/submissions/fa0e8fed-7d9f-4dab-8340-3671c29552b5

import Theorems.Thm_TeschlQM_Herglotz_poisson_lower_of_ball_density
import Theorems.Thm_TeschlQM_Herglotz_poisson_upper_of_ball_density
import Definitions.Def_TeschlQM_Herglotz_lowerDeriv
import Definitions.Def_TeschlQM_Herglotz_upperDeriv
import Mathlib.Tactic.FieldSimp

open MeasureTheory Filter Set
open scoped ENNReal Topology

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    TeschlQM.Herglotz.lowerDeriv μ t ≤ liminf (fun ε : ℝ => ENNReal.ofReal
        ((TeschlQM.Herglotz.borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi)) (𝓝[>] (0 : ℝ)) ∧
    liminf (fun ε : ℝ => ENNReal.ofReal
        ((TeschlQM.Herglotz.borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi)) (𝓝[>] (0 : ℝ)) ≤
      limsup (fun ε : ℝ => ENNReal.ofReal
        ((TeschlQM.Herglotz.borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi)) (𝓝[>] (0 : ℝ)) ∧
    limsup (fun ε : ℝ => ENNReal.ofReal
        ((TeschlQM.Herglotz.borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi)) (𝓝[>] (0 : ℝ)) ≤
      TeschlQM.Herglotz.upperDeriv μ t := by
  let density := fun r : ℝ => μ (Metric.ball t r) / volume (Metric.ball t r)
  let boundary := fun ε : ℝ => ENNReal.ofReal
    ((TeschlQM.Herglotz.borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi)
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hcutoff (δ c : ℝ) (hδ : 0 < δ) :
      Tendsto (fun ε : ℝ => ENNReal.ofReal (c * (2 / Real.pi * Real.arctan (δ / ε))))
        (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal c)) := by
    have hinv : Tendsto (fun ε : ℝ => δ / ε) (𝓝[>] (0 : ℝ)) atTop := by
      simpa only [div_eq_mul_inv, mul_comm] using
        (tendsto_inv_nhdsGT_zero : Tendsto (fun ε : ℝ => ε⁻¹) (𝓝[>] (0 : ℝ)) atTop).atTop_mul_const hδ
    have ha := (Real.tendsto_arctan_atTop.mono_right inf_le_left).comp hinv
    have hc := (ha.const_mul (2 / Real.pi)).const_mul c
    have heq : c * (2 / Real.pi * (Real.pi / 2)) = c := by
      field_simp [Real.pi_ne_zero]
    rw [heq] at hc
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hc
  refine ⟨?_, liminf_le_limsup, ?_⟩
  · change liminf density (𝓝[>] (0 : ℝ)) ≤ liminf boundary (𝓝[>] (0 : ℝ))
    apply (le_liminf_iff (u := boundary) (by isBoundedDefault) (by isBoundedDefault)).2
    intro y hy
    obtain ⟨c, hc, hyc, hcd⟩ := ENNReal.lt_iff_exists_real_btwn.1 hy
    have hd : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), ENNReal.ofReal c < density r :=
      eventually_lt_of_lt_liminf hcd
    obtain ⟨δ, hδ, hdδ⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hd
    have hb : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        y < ENNReal.ofReal (c * (2 / Real.pi * Real.arctan (δ / ε))) :=
      (hcutoff δ c hδ).eventually (lt_mem_nhds hyc)
    filter_upwards [hpos, hb] with ε hε hbε
    exact hbε.trans_le (ENNReal.ofReal_le_ofReal
      (TeschlQM.Herglotz.poisson_lower_of_ball_density μ t δ c ε hδ hc hε
        (fun r hr hrδ => (hdδ ⟨hr, hrδ⟩).le)))
  · change limsup boundary (𝓝[>] (0 : ℝ)) ≤ limsup density (𝓝[>] (0 : ℝ))
    apply (limsup_le_iff (u := boundary) (by isBoundedDefault) (by isBoundedDefault)).2
    intro y hy
    obtain ⟨c, hc, hdc, hcy⟩ := ENNReal.lt_iff_exists_real_btwn.1 hy
    have hd : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), density r < ENNReal.ofReal c :=
      eventually_lt_of_limsup_lt hdc
    obtain ⟨δ, hδ, hdδ⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hd
    have htail : Tendsto (fun ε : ℝ => ENNReal.ofReal
        (c + (ε / δ ^ 2) * (μ Set.univ).toReal / Real.pi))
        (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal c)) := by
      have hz : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_right inf_le_left
      have hh := ((((hz.div_const (δ ^ 2)).mul_const
        (μ Set.univ).toReal).div_const Real.pi).const_add c)
      simp only [zero_div, zero_mul, add_zero] at hh
      exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh
    have hb := htail.eventually (gt_mem_nhds hcy)
    filter_upwards [hpos, hb] with ε hε hbε
    exact (ENNReal.ofReal_le_ofReal
      (TeschlQM.Herglotz.poisson_upper_of_ball_density μ t δ c ε hδ hc hε
        (fun r hr hrδ => (hdδ ⟨hr, hrδ⟩).le))).trans_lt hbε
