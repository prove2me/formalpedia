-- Prove2me | solution 1 for PoissonDirichlet.Moments.eq_86
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:48:02.982987+00:00
-- url     : https://prove2.me/submissions/0057bd76-2feb-4192-a611-cff17f15867c

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology


namespace PoissonDirichlet.Moments

open Set

/-- Gamma-type identity in lintegral form: for `x > 0`,
`∫_0^∞ t^{p-1} e^{-tx} dt = Γ(p) x^{-p}`. -/
lemma e86_gamma (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 1) * Real.exp (-t * x)) =
      ENNReal.ofReal (Real.Gamma p * x ^ (-p)) := by
  have hint : ∫ t in Ioi (0:ℝ), t ^ (p - 1) * Real.exp (-t * x) = Real.Gamma p * x ^ (-p) := by
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi hp hx
    have e : (fun t : ℝ => t ^ (p - 1) * Real.exp (-t * x)) =
        fun t : ℝ => t ^ (p - 1) * Real.exp (-(x * t)) := by
      funext t; ring_nf
    rw [e, this, one_div, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]; ring
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] fun t : ℝ => t ^ (p - 1) * Real.exp (-t * x) := by
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    have : (0:ℝ) < t := ht
    positivity
  have hm : AEStronglyMeasurable (fun t : ℝ => t ^ (p - 1) * Real.exp (-t * x))
      (volume.restrict (Ioi (0:ℝ))) := by fun_prop
  have h1 := integral_eq_lintegral_of_nonneg_ae hnn hm
  rw [hint] at h1
  have hpos : 0 < Real.Gamma p * x ^ (-p) := by
    have := Real.Gamma_pos_of_pos hp
    positivity
  have hne : ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 1) * Real.exp (-t * x)) ≠ ⊤ := by
    intro h
    rw [h, ENNReal.toReal_top] at h1
    linarith
  rw [h1, ENNReal.ofReal_toReal hne]

theorem eq_86_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hXm : AEMeasurable X P) (hX : ∀ᵐ ω ∂P, 0 < X ω) (p : ℝ) (hp : 0 < p) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ (-p)) ∂P =
      ENNReal.ofReal (1 / Real.Gamma p) *
        ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 1) * ∫ ω, Real.exp (-t * X ω) ∂P) := by
  have hG : 0 < Real.Gamma p := Real.Gamma_pos_of_pos hp
  -- Step 1: rewrite the integrand through the Gamma identity
  have step1 : ∫⁻ ω, ENNReal.ofReal (X ω ^ (-p)) ∂P =
      ∫⁻ ω, ENNReal.ofReal (1 / Real.Gamma p) *
        ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 1) * Real.exp (-t * X ω)) ∂(volume : Measure ℝ) ∂P := by
    refine lintegral_congr_ae (hX.mono fun ω hω => ?_)
    show ENNReal.ofReal (X ω ^ (-p)) = ENNReal.ofReal (1 / Real.Gamma p) *
      ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 1) * Real.exp (-t * X ω))
    rw [e86_gamma p (X ω) hp hω, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [step1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  -- Step 2: Tonelli
  have hmeas : AEMeasurable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      ENNReal.ofReal (t ^ (p - 1) * Real.exp (-t * X ω))) (P.prod (volume.restrict (Ioi (0:ℝ)))) := by
    have h1 : AEMeasurable (fun z : Ω × ℝ => X z.1) (P.prod (volume.restrict (Ioi (0:ℝ)))) :=
      hXm.comp_fst
    have h2 : AEMeasurable (fun z : Ω × ℝ => z.2) (P.prod (volume.restrict (Ioi (0:ℝ)))) :=
      measurable_snd.aemeasurable
    have h3 : AEMeasurable (fun z : Ω × ℝ => z.2 ^ (p - 1) * Real.exp (-z.2 * X z.1))
        (P.prod (volume.restrict (Ioi (0:ℝ)))) := by
      apply AEMeasurable.mul
      · exact h2.pow_const _
      · exact Real.measurable_exp.comp_aemeasurable (h2.neg.mul h1)
    exact h3.ennreal_ofReal
  rw [lintegral_lintegral_swap hmeas]
  refine lintegral_congr_ae ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_)
  have ht0 : (0:ℝ) < t := ht
  -- Step 3: pull out t^(p-1) and convert the inner lintegral to a Bochner integral
  have hint : Integrable (fun ω => Real.exp (-t * X ω)) P := by
    refine Integrable.mono' (integrable_const (1:ℝ))
      (Real.measurable_exp.comp_aemeasurable (hXm.const_mul (-t))).aestronglyMeasurable ?_
    refine hX.mono fun ω hω => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    nlinarith
  have hnn : 0 ≤ᵐ[P] fun ω => Real.exp (-t * X ω) :=
    Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le
  show ∫⁻ ω, ENNReal.ofReal (t ^ (p - 1) * Real.exp (-t * X ω)) ∂P =
    ENNReal.ofReal (t ^ (p - 1) * ∫ ω, Real.exp (-t * X ω) ∂P)
  rw [ENNReal.ofReal_mul (by positivity), ofReal_integral_eq_lintegral_ofReal hint hnn,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ω => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]

end PoissonDirichlet.Moments

open PoissonDirichlet.Moments


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hXm : AEMeasurable X P) (hX : ∀ᵐ ω ∂P, 0 < X ω) (p : ℝ) (hp : 0 < p) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ (-p)) ∂P =
      ENNReal.ofReal (1 / Real.Gamma p) *
        ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 1) * ∫ ω, Real.exp (-t * X ω) ∂P) := by
  exact eq_86_core P X hXm hX p hp
