-- Prove2me | solution 1 for SAARate.SharpLD.display_3_11
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:12:27.836418+00:00
-- url     : https://prove2.me/submissions/bff48c4e-2b1e-45e1-b59f-de36a7e0b43d

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

theorem display_3_11 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) (κ : ℝ)
    (hXκ : ∀ᵐ ω ∂P, |X ω| ≤ κ) :
    ∀ t : ℝ,
      deriv (deriv (cgf X P)) t =
          (∫ ω, X ω ^ 2 * Real.exp (t * X ω) ∂P) / mgf X P t - (deriv (cgf X P) t) ^ 2 ∧
        |(∫ ω, X ω ^ 2 * Real.exp (t * X ω) ∂P) / mgf X P t - (deriv (cgf X P) t) ^ 2| ≤
          |κ ^ 2 - (deriv (cgf X P) t) ^ 2| ∧
        |κ ^ 2 - (deriv (cgf X P) t) ^ 2| ≤ κ ^ 2 := by
  intro t
  have hi : deriv (deriv (cgf X P)) t =
      (∫ ω, X ω ^ 2 * Real.exp (t * X ω) ∂P) / mgf X P t - (deriv (cgf X P) t) ^ 2 := by
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using
      iteratedDeriv_two_cgf (exp_interior P X hX κ hXκ t)
  obtain ⟨hn, hu⟩ := second_bounds P X hX κ hXκ t
  have hk : 0 ≤ κ ^ 2 - (deriv (cgf X P) t) ^ 2 := hn.trans hu
  refine ⟨hi, ?_, ?_⟩
  · rw [← hi, abs_of_nonneg hn, abs_of_nonneg hk]
    exact hu
  · rw [abs_of_nonneg hk]
    exact sub_le_self _ (sq_nonneg _)


end SAARate.SharpLD

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) (κ : ℝ)
    (hXκ : ∀ᵐ ω ∂P, |X ω| ≤ κ) :
    ∀ t : ℝ,
      deriv (deriv (cgf X P)) t =
          (∫ ω, X ω ^ 2 * Real.exp (t * X ω) ∂P) / mgf X P t - (deriv (cgf X P) t) ^ 2 ∧
        |(∫ ω, X ω ^ 2 * Real.exp (t * X ω) ∂P) / mgf X P t - (deriv (cgf X P) t) ^ 2| ≤
          |κ ^ 2 - (deriv (cgf X P) t) ^ 2| ∧
        |κ ^ 2 - (deriv (cgf X P) t) ^ 2| ≤ κ ^ 2  := by
  exact SAARate.SharpLD.display_3_11 P X hX κ hXκ

#print axioms solution
