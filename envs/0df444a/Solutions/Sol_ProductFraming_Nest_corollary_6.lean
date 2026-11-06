-- Prove2me | solution 1 for ProductFraming.Nest.corollary_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T07:13:25.31537+00:00
-- url     : https://prove2.me/submissions/a4bf4f93-9be6-4c12-8c87-83463192037d

import Mathlib
import Definitions.Def_ProductFraming_Nest_Model
import Theorems.Thm_ProductFraming_Nest_lemma_7
import Theorems.Thm_ProductFraming_Nest_corollary_5

open MeasureTheory ProbabilityTheory Set Real Filter Topology

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
namespace PFNConvAux

/-- `h(t) = t / (1 - e^{-t})` for `t > 0`, extended by its limit `1` at `0` (and by `1` for `t ≤ 0`). -/
noncomputable def h (t : ℝ) : ℝ := if t ≤ 0 then 1 else t / (1 - exp (-t))

lemma one_sub_exp_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - exp (-t) := by
  have : exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

lemma h_pos_eq {t : ℝ} (ht : 0 < t) : h t = t / (1 - exp (-t)) := by
  simp [h, not_le.mpr ht]

/-- `k(t) = t (1 + e^{-t}) - 2 (1 - e^{-t}) ≥ 0` on `[0, ∞)`. -/
lemma k_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ t * (1 + exp (-t)) - 2 * (1 - exp (-t)) := by
  set k : ℝ → ℝ := fun t => t * (1 + exp (-t)) - 2 * (1 - exp (-t)) with hk
  have hd : ∀ x, HasDerivAt k (1 - (1 + x) * exp (-x)) x := by
    intro x
    have he : HasDerivAt (fun t => exp (-t)) (exp (-x) * (-1)) x := (hasDerivAt_neg x).exp
    have := ((hasDerivAt_id x).mul ((hasDerivAt_const x (1 : ℝ)).add he)).sub
      ((hasDerivAt_const x (1 : ℝ)).sub he |>.const_mul 2)
    exact this.congr_deriv (by simp; ring)
  have hmono : MonotoneOn k (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt).continuousOn
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      have h1 : 1 + x ≤ exp x := by linarith [add_one_le_exp x]
      have h2 : (1 + x) * exp (-x) ≤ exp x * exp (-x) :=
        mul_le_mul_of_nonneg_right h1 (exp_pos _).le
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h2
      linarith
  have := hmono (self_mem_Ici) ht ht
  simpa [hk] using this

lemma tendsto_h_zero : Tendsto (fun t => t / (1 - exp (-t))) (𝓝[>] 0) (𝓝 1) := by
  have hd : HasDerivAt (fun t => 1 - exp (-t)) 1 0 := by
    have := ((hasDerivAt_neg (0 : ℝ)).exp).const_sub 1
    simpa using this
  have hs := hd.tendsto_slope_zero_right
  simp only [zero_add, neg_zero, Real.exp_zero, sub_self, sub_zero, smul_eq_mul] at hs
  have hs' : Tendsto (fun t => (1 - exp (-t)) / t) (𝓝[>] 0) (𝓝 1) := by
    refine hs.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [inv_mul_eq_div]
  have := hs'.inv₀ one_ne_zero
  simp only [inv_one] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t _
  rw [inv_div]

lemma h_continuousOn : ContinuousOn h (Ici 0) := by
  intro t ht
  rcases (mem_Ici.mp ht).lt_or_eq with hpos | hzero
  · apply ContinuousAt.continuousWithinAt
    have hc : ContinuousAt (fun t => t / (1 - exp (-t))) t :=
      ContinuousAt.div continuousAt_id (by fun_prop) (one_sub_exp_pos hpos).ne'
    refine hc.congr ?_
    filter_upwards [lt_mem_nhds hpos] with s hs
    rw [h_pos_eq hs]
  · subst hzero
    rw [ContinuousWithinAt, show h 0 = 1 by simp [h]]
    have hI : 𝓝[Ici (0 : ℝ)] 0 = 𝓝[>] 0 ⊔ pure 0 := by
      rw [← Ioi_insert, nhdsWithin_insert, sup_comm]
    rw [hI, tendsto_sup]
    refine ⟨?_, ?_⟩
    swap
    · rw [tendsto_pure_left]
      intro s hs
      have : (1 : ℝ) ∈ s := mem_of_mem_nhds hs
      simpa [h] using this
    refine tendsto_h_zero.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [h_pos_eq hs]

lemma h_convexOn : ConvexOn ℝ (Ici 0) h := by
  set f' : ℝ → ℝ := fun t => (1 - exp (-t) - t * exp (-t)) / (1 - exp (-t)) ^ 2 with hf'
  set f'' : ℝ → ℝ := fun t =>
    exp (-t) * (t * (1 + exp (-t)) - 2 * (1 - exp (-t))) / (1 - exp (-t)) ^ 3 with hf''
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := f') (f'' := f'') (convex_Ici 0) h_continuousOn
  · intro x hx
    rw [interior_Ici] at hx
    have hpos : 0 < 1 - exp (-x) := one_sub_exp_pos hx
    have he : HasDerivAt (fun t => exp (-t)) (exp (-x) * (-1)) x := (hasDerivAt_neg x).exp
    have hD : HasDerivAt (fun t => 1 - exp (-t)) (exp (-x)) x := by
      have := (hasDerivAt_const x (1 : ℝ)).sub he
      exact this.congr_deriv (by ring)
    have hq : HasDerivAt (fun t => t / (1 - exp (-t))) (f' x) x := by
      have := (hasDerivAt_id x).div hD hpos.ne'
      exact this.congr_deriv (by simp only [hf', id]; field_simp)
    apply HasDerivAt.hasDerivWithinAt
    refine hq.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hx] with s hs
    rw [h_pos_eq hs]
  · intro x hx
    rw [interior_Ici] at hx
    have hpos : 0 < 1 - exp (-x) := one_sub_exp_pos hx
    have he : HasDerivAt (fun t => exp (-t)) (exp (-x) * (-1)) x := (hasDerivAt_neg x).exp
    have hD : HasDerivAt (fun t => 1 - exp (-t)) (exp (-x)) x := by
      have := (hasDerivAt_const x (1 : ℝ)).sub he
      exact this.congr_deriv (by ring)
    have hN : HasDerivAt (fun t => 1 - exp (-t) - t * exp (-t)) (x * exp (-x)) x := by
      have := (hD.sub ((hasDerivAt_id x).mul he))
      exact this.congr_deriv (by simp)
    have hD2 : HasDerivAt (fun t => (1 - exp (-t)) ^ 2) (2 * (1 - exp (-x)) * exp (-x)) x := by
      have := hD.pow 2
      exact this.congr_deriv (by norm_num)
    have := hN.div hD2 (pow_ne_zero 2 hpos.ne')
    apply HasDerivAt.hasDerivWithinAt
    exact this.congr_deriv (by simp only [hf'']; field_simp; ring)
  · intro x hx
    rw [interior_Ici] at hx
    have hpos : 0 < 1 - exp (-x) := one_sub_exp_pos hx
    exact div_nonneg (mul_nonneg (exp_pos _).le (k_nonneg hx.le)) (pow_nonneg hpos.le 3)

lemma one_le_h {t : ℝ} (ht : 0 ≤ t) : 1 ≤ h t := by
  rcases ht.lt_or_eq with hpos | hzero
  · rw [h_pos_eq hpos, le_div_iff₀ (one_sub_exp_pos hpos)]
    have := add_one_le_exp (-t)
    linarith
  · subst hzero; simp [h]

lemma h_le {t : ℝ} (ht : 0 ≤ t) : h t ≤ 1 + t := by
  rcases ht.lt_or_eq with hpos | hzero
  · rw [h_pos_eq hpos, div_le_iff₀ (one_sub_exp_pos hpos)]
    -- `(1 + t) e^{-t} ≤ 1`
    have h1 : 1 + t ≤ exp t := by linarith [add_one_le_exp t]
    have h2 : (1 + t) * exp (-t) ≤ exp t * exp (-t) := mul_le_mul_of_nonneg_right h1 (exp_pos _).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h2
    nlinarith
  · subst hzero; simp [h]

lemma h_monotoneOn : MonotoneOn h (Ici 0) := by
  intro a ha b hb hab
  rcases (mem_Ici.mp ha).lt_or_eq with hapos | hazero
  · -- `a = (1 - θ) · 0 + θ · b` with `θ = a / b`
    have hbpos : 0 < b := lt_of_lt_of_le hapos hab
    have hθ0 : 0 ≤ a / b := div_nonneg hapos.le hbpos.le
    have hθ1 : a / b ≤ 1 := (div_le_one hbpos).mpr hab
    have hc := h_convexOn.2 (self_mem_Ici) hb (sub_nonneg.mpr hθ1) hθ0 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add] at hc
    rw [div_mul_cancel₀ a hbpos.ne'] at hc
    have h0 : h 0 = 1 := by simp [h]
    rw [h0] at hc
    have := one_le_h hb
    nlinarith
  · subst hazero
    rw [show h 0 = 1 by simp [h]]
    exact one_le_h hb

lemma h_measurable : Measurable h := by
  unfold h
  exact Measurable.ite measurableSet_Iic measurable_const (by fun_prop)

end PFNConvAux

open Finset ProductFraming.Nest

open PFNExpAux PFNConvAux in
theorem solution (m : ℕ) (hm : 1 ≤ m) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) (hA3 : IsNBUE m lam) :
    ∑ x ∈ Icc 1 m, lam x * (x : ℝ) / Emin m lam (x : ℝ) ≤
      ∫ w, w / (∫ z, min z w ∂(expMeasure (mean m lam)⁻¹)) ∂(expMeasure (mean m lam)⁻¹) := by
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
  set g : ℝ → ℝ := fun w => h (w / μ) with hg
  have hmono : MonotoneOn g (Ici 0) := by
    intro a ha b hb hab
    exact h_monotoneOn (mem_Ici.mpr (div_nonneg (mem_Ici.mp ha) hμpos.le))
      (mem_Ici.mpr (div_nonneg (mem_Ici.mp hb) hμpos.le)) (div_le_div_of_nonneg_right hab hμpos.le)
  have hconv : ConvexOn ℝ (Ici 0) g := by
    refine ⟨convex_Ici 0, fun a ha b hb s t hs ht hst => ?_⟩
    have ha' : a / μ ∈ Ici (0 : ℝ) := mem_Ici.mpr (div_nonneg (mem_Ici.mp ha) hμpos.le)
    have hb' : b / μ ∈ Ici (0 : ℝ) := mem_Ici.mpr (div_nonneg (mem_Ici.mp hb) hμpos.le)
    have := h_convexOn.2 ha' hb' hs ht hst
    simp only [hg, smul_eq_mul] at this ⊢
    rw [show (s * a + t * b) / μ = s * (a / μ) + t * (b / μ) by ring]
    exact this
  -- `W > 0` almost surely
  have hpos : ∀ᵐ w ∂(expMeasure μ⁻¹), 0 < w := by
    have h0 : ∀ᵐ w ∂(expMeasure μ⁻¹), w ≠ 0 := by
      rw [ae_iff]
      simp only [ne_eq, not_not]
      have hac : expMeasure μ⁻¹ ≪ volume := by
        rw [expMeasure, gammaMeasure]; exact withDensity_absolutelyContinuous _ _
      exact hac (by simp)
    filter_upwards [h0, ae_nonneg_expMeasure μ⁻¹] with w h1 h2
    exact lt_of_le_of_ne h2 (Ne.symm h1)
  have hgint : Integrable g (expMeasure μ⁻¹) := by
    have hb : Integrable (fun w : ℝ => 1 + w * μ⁻¹) (expMeasure μ⁻¹) :=
      (integrable_const 1).add ((integrable_id_expMeasure hr).mul_const μ⁻¹)
    refine hb.mono' ?_ ?_
    · exact (h_measurable.comp (measurable_id.div_const μ)).aestronglyMeasurable
    · filter_upwards [ae_nonneg_expMeasure μ⁻¹] with w hw
      have hw' : 0 ≤ w / μ := div_nonneg hw hμpos.le
      rw [Real.norm_of_nonneg (le_trans zero_le_one (one_le_h hw'))]
      have := h_le hw'
      rw [div_eq_mul_inv] at this
      exact this
  have h7 := lemma_7 m hm lam hlam hA3 g hmono hconv hgint
  have hc5 := corollary_5 m hm lam hlam hA3
  -- the inner integral
  have hinner : ∀ w : ℝ, 0 < w → ∫ z, min z w ∂(expMeasure μ⁻¹) = μ * (1 - exp (-(w / μ))) := by
    intro w hw
    rw [integral_min_expMeasure hr hw.le, div_inv_eq_mul, mul_comm, inv_mul_eq_div]
  have hgw : ∀ w : ℝ, 0 < w → g w = w / (∫ z, min z w ∂(expMeasure μ⁻¹)) := by
    intro w hw
    rw [hinner w hw]
    simp only [hg]
    rw [h_pos_eq (div_pos hw hμpos)]
    field_simp
  have hRHS : ∫ w, g w ∂(expMeasure μ⁻¹) = ∫ w, w / (∫ z, min z w ∂(expMeasure μ⁻¹)) ∂(expMeasure μ⁻¹) := by
    apply integral_congr_ae
    filter_upwards [hpos] with w hw
    exact hgw w hw
  rw [← hRHS]
  refine le_trans (sum_le_sum fun x hx => ?_) h7
  have hx1 : (0 : ℝ) < x := by exact_mod_cast (Finset.mem_Icc.mp hx).1
  have he : 0 < ∫ z, min z (x : ℝ) ∂(expMeasure μ⁻¹) := by
    rw [hinner x hx1]
    exact mul_pos hμpos (one_sub_exp_pos (div_pos hx1 hμpos))
  have hle := hc5 x hx1.le
  rw [hgw x hx1, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (hlam.1 x hx)
  exact div_le_div_of_nonneg_left hx1.le he hle
