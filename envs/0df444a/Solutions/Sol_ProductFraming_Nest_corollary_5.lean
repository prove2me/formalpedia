-- Prove2me | solution 1 for ProductFraming.Nest.corollary_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T07:10:23.066093+00:00
-- url     : https://prove2.me/submissions/db6de49f-f395-4c2e-b756-df36c005436d

import Mathlib
import Definitions.Def_ProductFraming_Nest_Model
import Theorems.Thm_ProductFraming_Nest_lemma_7

open MeasureTheory ProbabilityTheory Set Real

namespace PFNExpAux

lemma integral_expMeasure {r : ℝ} (hr : 0 < r) (f : ℝ → ℝ) :
    ∫ x, f x ∂(expMeasure r) = ∫ x in Ioi 0, r * exp (-(r * x)) * f x := by
  show ∫ x, f x ∂(volume.withDensity (fun x => ENNReal.ofReal (gammaPDFReal 1 r x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
      ((measurable_gammaPDFReal 1 r).ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
  congr 1
  ext x
  simp only [smul_eq_mul, indicator]
  rw [ENNReal.toReal_ofReal (gammaPDFReal_nonneg one_pos hr x)]
  unfold gammaPDFReal
  split_ifs with h1 h2 h2
  · simp
  · exact absurd (mem_Ici.mpr h1) h2
  · exact absurd (mem_Ici.mp h2) h1
  · simp

lemma ae_nonneg_expMeasure (r : ℝ) : ∀ᵐ w ∂(expMeasure r), 0 ≤ w := by
  rw [ae_iff]
  simp only [not_le]
  show expMeasure r (Iio 0) = 0
  rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iio]
  rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0) (fun x hx => gammaPDF_of_neg hx)]
  simp

/-- `E[min(Z, w)] = (1 - e^{-r w}) / r` for `Z` exponential with rate `r` and `w ≥ 0`. -/
lemma integral_min_expMeasure {r : ℝ} (hr : 0 < r) {w : ℝ} (hw : 0 ≤ w) :
    ∫ z, min z w ∂(expMeasure r) = (1 - exp (-(r * w))) / r := by
  rw [integral_expMeasure hr]
  have hint1 : IntegrableOn (fun z => r * exp (-(r * z)) * min z w) (Ioc 0 w) := by
    apply ContinuousOn.integrableOn_Icc ?_ |>.mono_set Ioc_subset_Icc_self
    fun_prop
  have hint2 : IntegrableOn (fun z => r * exp (-(r * z)) * min z w) (Ioi w) := by
    have : IntegrableOn (fun z => r * w * exp (-r * z)) (Ioi w) :=
      (exp_neg_integrableOn_Ioi w hr).const_mul (r * w)
    refine this.congr_fun (fun z hz => ?_) measurableSet_Ioi
    simp only
    rw [min_eq_right (le_of_lt (mem_Ioi.mp hz))]
    ring_nf
  rw [← Ioc_union_Ioi_eq_Ioi hw, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    hint1 hint2]
  have h1 : ∫ z in Ioc 0 w, r * exp (-(r * z)) * min z w
      = ∫ z in Ioc 0 w, r * z * exp (-(r * z)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    simp only
    rw [min_eq_left hz.2]; ring
  have h2 : ∫ z in Ioi w, r * exp (-(r * z)) * min z w
      = ∫ z in Ioi w, (r * w) * exp ((-r) * z) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    simp only
    rw [min_eq_right (le_of_lt (mem_Ioi.mp hz))]; ring_nf
  rw [h1, h2, integral_const_mul, integral_exp_mul_Ioi (by linarith)]
  rw [← intervalIntegral.integral_of_le hw]
  have hderiv : ∀ x ∈ uIcc 0 w, HasDerivAt (fun z => -z * exp (-(r * z)) - exp (-(r * z)) / r)
      (r * x * exp (-(r * x))) x := by
    intro x _
    have he : HasDerivAt (fun z => exp (-(r * z))) (exp (-(r * x)) * (-r)) x := by
      have := ((hasDerivAt_id x).const_mul r).neg.exp
      simpa using this
    have := ((hasDerivAt_neg x).mul he).sub (he.div_const r)
    have h' := this.congr_deriv (show _ = r * x * exp (-(r * x)) by field_simp; ring)
    exact h'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  field_simp
  ring_nf
  rw [Real.exp_zero]; ring

/-- `E[Z] = 1/r` for `Z` exponential with rate `r`. -/
lemma integral_id_expMeasure {r : ℝ} (hr : 0 < r) : ∫ z, z ∂(expMeasure r) = r⁻¹ := by
  rw [integral_expMeasure hr]
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) hr
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.Gamma_two, mul_one] at h
  simp only [Real.rpow_one] at h
  have : ∫ z in Ioi (0 : ℝ), r * exp (-(r * z)) * z = r * ∫ z in Ioi (0 : ℝ), z * exp (-(r * z)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z _; simp only; ring
  rw [this, h]
  norm_num [Real.rpow_two, div_pow]
  field_simp

lemma integrable_id_expMeasure {r : ℝ} (hr : 0 < r) : Integrable (fun z : ℝ => z) (expMeasure r) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_id_expMeasure hr]
  exact (inv_pos.mpr hr).ne'

end PFNExpAux

open Finset ProductFraming.Nest

open PFNExpAux in
theorem solution (m : ℕ) (hm : 1 ≤ m) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) (hA3 : IsNBUE m lam) :
    ∀ x : ℝ, 0 ≤ x → ∫ z, min z x ∂(expMeasure (mean m lam)⁻¹) ≤ Emin m lam x := by
  intro x _
  set μ := mean m lam with hμ
  have hμ1 : 1 ≤ μ := by
    rw [hμ, mean, ← hlam.2]
    apply sum_le_sum
    intro y hy
    have : (1 : ℝ) ≤ y := by exact_mod_cast (Finset.mem_Icc.mp hy).1
    nlinarith [hlam.1 y hy]
  have hμpos : 0 < μ := by linarith
  have hr : 0 < μ⁻¹ := inv_pos.mpr hμpos
  haveI := isProbabilityMeasure_expMeasure hr
  set g : ℝ → ℝ := fun w => max (w - x) 0 with hg
  have hmono : MonotoneOn g (Ici 0) := by
    intro a _ b _ hab
    simp only [hg]
    exact max_le_max (by linarith) le_rfl
  have hconv : ConvexOn ℝ (Ici 0) g := by
    have h1 : ConvexOn ℝ (Ici (0 : ℝ)) (fun w : ℝ => w - x) :=
      (convexOn_id (convex_Ici 0)).sub (concaveOn_const x (convex_Ici 0))
    have h2 : ConvexOn ℝ (Ici (0 : ℝ)) (fun _ : ℝ => (0 : ℝ)) := convexOn_const 0 (convex_Ici 0)
    exact h1.sup h2
  have hid := integrable_id_expMeasure hr
  have hgint : Integrable g (expMeasure μ⁻¹) := by
    have : Integrable (fun w : ℝ => w - x) (expMeasure μ⁻¹) := hid.sub (integrable_const x)
    exact this.sup (integrable_const 0)
  have h7 := lemma_7 m hm lam hlam hA3 g hmono hconv hgint
  -- `min(w, x) = w - (w - x)^+`
  have hmin : ∀ w : ℝ, min w x = w - g w := by
    intro w; simp only [hg]
    rcases le_total w x with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  have hL : ∫ z, min z x ∂(expMeasure μ⁻¹) = μ - ∫ z, g z ∂(expMeasure μ⁻¹) := by
    simp_rw [hmin]
    rw [integral_sub hid hgint, integral_id_expMeasure hr, inv_inv]
  have hR : Emin m lam x = μ - ∑ y ∈ Finset.Icc 1 m, lam y * g y := by
    unfold Emin
    rw [hμ, mean, ← sum_sub_distrib]
    apply sum_congr rfl
    intro y _
    rw [hmin]; ring
  rw [hL, hR]
  linarith
