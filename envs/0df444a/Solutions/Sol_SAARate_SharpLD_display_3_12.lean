-- Prove2me | solution 1 for SAARate.SharpLD.display_3_12
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:12:29.838352+00:00
-- url     : https://prove2.me/submissions/a08e23b4-210e-4b85-95a8-eae8420e93d7

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology

private theorem exp_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) (κ : ℝ)
    (hb : ∀ᵐ ω ∂P, |X ω| ≤ κ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * X ω)) P := by
  refine (integrable_const (Real.exp (|t| * κ))).mono' (by fun_prop) ?_
  filter_upwards [hb] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    t * X ω ≤ |t * X ω| := le_abs_self _
    _ = |t| * |X ω| := abs_mul _ _
    _ ≤ |t| * κ := mul_le_mul_of_nonneg_left hω (abs_nonneg _)

private theorem exp_interior {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) (κ : ℝ)
    (hb : ∀ᵐ ω ∂P, |X ω| ≤ κ) (t : ℝ) :
    t ∈ interior (integrableExpSet X P) := by
  have he : integrableExpSet X P = Set.univ := by
    ext u
    simp only [Set.mem_univ, iff_true]
    exact exp_integrable P X hX κ hb u
  simp [he]

private theorem second_bounds {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) (κ : ℝ)
    (hb : ∀ᵐ ω ∂P, |X ω| ≤ κ) (t : ℝ) :
    0 ≤ deriv (deriv (cgf X P)) t ∧
    deriv (deriv (cgf X P)) t ≤ κ ^ 2 - (deriv (cgf X P) t) ^ 2 := by
  have ht := exp_interior P X hX κ hb t
  let Q := P.tilted (fun ω => t * X ω)
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_tilted (exp_integrable P X hX κ hb t)
  have hQ : ∀ᵐ ω ∂Q, X ω ∈ Set.Icc (-κ) κ :=
    (tilted_absolutelyContinuous P _).ae_le (hb.mono fun ω hω => abs_le.mp hω)
  have hm : AEMeasurable X Q := hX.aemeasurable
  have hv : variance X Q = deriv (deriv (cgf X P)) t := by
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using variance_tilted_mul ht
  have hd : (∫ ω, X ω ∂Q) = deriv (cgf X P) t := integral_tilted_mul_self ht
  refine ⟨hv ▸ variance_nonneg X Q, ?_⟩
  have hh := variance_le_sub_mul_sub hQ hm
  rw [hv, hd] at hh
  nlinarith

namespace SAARate.SharpLD

theorem display_3_12 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) (κ : ℝ)
    (hXκ : ∀ᵐ ω ∂P, |X ω| ≤ κ) :
    ∀ t s : ℝ, |deriv (cgf X P) t - deriv (cgf X P) s| ≤ κ ^ 2 * |t - s| := by
  intro t s
  have hdiff : ∀ u : ℝ, DifferentiableAt ℝ (deriv (cgf X P)) u :=
    fun u => (analyticAt_cgf (exp_interior P X hX κ hXκ u)).deriv.differentiableAt
  have hbound : ∀ u : ℝ, ‖deriv (deriv (cgf X P)) u‖ ≤ κ ^ 2 := by
    intro u
    obtain ⟨hn, hu⟩ := second_bounds P X hX κ hXκ u
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact hu.trans (sub_le_self _ (sq_nonneg _))
  simpa only [Real.norm_eq_abs] using
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun u (_ : u ∈ Set.univ) => hdiff u)
      (fun u (_ : u ∈ Set.univ) => hbound u) (Set.mem_univ s) (Set.mem_univ t)


end SAARate.SharpLD

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) (κ : ℝ)
    (hXκ : ∀ᵐ ω ∂P, |X ω| ≤ κ) :
    ∀ t s : ℝ, |deriv (cgf X P) t - deriv (cgf X P) s| ≤ κ ^ 2 * |t - s|  := by
  exact SAARate.SharpLD.display_3_12 P X hX κ hXκ

#print axioms solution
