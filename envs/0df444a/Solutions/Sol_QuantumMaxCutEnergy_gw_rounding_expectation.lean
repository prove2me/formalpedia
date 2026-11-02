-- Prove2me | solution 1 for QuantumMaxCutEnergy.gw_rounding_expectation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T23:05:22.730106+00:00
-- url     : https://prove2.me/submissions/f114d5c8-be7d-413f-a331-a7e31dbab462

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace QuantumMaxCutEnergy

namespace GWa

variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

/-! ### Basic measurability of `Real.sign` -/

lemma measurable_real_sign : Measurable (fun x : ℝ => Real.sign x) := by
  have h : (fun x : ℝ => Real.sign x) =
      fun x => if x < 0 then (-1:ℝ) else if x = 0 then 0 else 1 := by
    funext x
    rcases lt_trichotomy x 0 with hx | hx | hx
    · rw [if_pos hx, Real.sign_of_neg hx]
    · subst hx; simp
    · rw [if_neg (by linarith), if_neg (by linarith), Real.sign_of_pos hx]
  rw [h]
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const ?_
  exact Measurable.ite (measurableSet_singleton 0) measurable_const measurable_const

lemma measurable_sign_inner (u : E) :
    Measurable (fun g : E => Real.sign (inner ℝ u g)) :=
  measurable_real_sign.comp (by fun_prop)

lemma measurable_indicator_sign (u w : E) :
    Measurable (fun g : E => if Real.sign (inner ℝ u g) = Real.sign (inner ℝ w g)
      then (0:ℝ) else 1) := by
  have hset : MeasurableSet {g : E | Real.sign (inner ℝ u g) = Real.sign (inner ℝ w g)} :=
    measurableSet_eq_fun (measurable_sign_inner u) (measurable_sign_inner w)
  exact Measurable.ite hset measurable_const measurable_const

lemma measurable_indicator_sign_ne (u w : E) :
    Measurable (fun g : E => if Real.sign (inner ℝ u g) ≠ Real.sign (inner ℝ w g)
      then (1:ℝ) else 0) := by
  have hset : MeasurableSet {g : E | Real.sign (inner ℝ u g) ≠ Real.sign (inner ℝ w g)} :=
    (measurableSet_eq_fun (measurable_sign_inner u) (measurable_sign_inner w)).compl
  exact Measurable.ite hset measurable_const measurable_const

/-! ### Law of a coordinate functional and nullity of hyperplanes -/

/-- The law of `g ↦ ⟪u, g⟫` under the standard Gaussian is the standard normal. -/
lemma map_inner_stdGaussian (u : E) (hu : ‖u‖ = 1) :
    (stdGaussian E).map (fun g => inner ℝ u g) = gaussianReal 0 1 := by
  have hm : Measurable (fun g : E => inner ℝ u g) := by fun_prop
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_apply, integral_map hm.aemeasurable (by fun_prop)]
  have h1 : ∀ g : E,
      Complex.exp (↑(inner ℝ (inner ℝ u g) t) * Complex.I)
        = Complex.exp (↑(inner ℝ g (t • u)) * Complex.I) := by
    intro g
    have hval : inner ℝ (inner ℝ u g) t = inner ℝ g (t • u) := by
      rw [real_inner_smul_right, real_inner_comm g u]
      simp
    rw [hval]
  simp only [h1, ← charFun_apply]
  rw [charFun_stdGaussian, charFun_gaussianReal]
  simp only [NNReal.coe_one, Complex.ofReal_one, Complex.ofReal_zero, mul_zero, zero_mul,
    one_mul]
  have h2 : ‖t • u‖ = |t| := by rw [norm_smul, Real.norm_eq_abs, hu, mul_one]
  rw [h2]
  congr 1
  have h3 : (↑|t| : ℂ) ^ 2 = (↑t : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]
  rw [h3]
  ring

/-- The hyperplane `{g | ⟪u, g⟫ = 0}` is null for the standard Gaussian. -/
lemma measure_inner_eq_zero (u : E) (hu : ‖u‖ = 1) :
    stdGaussian E {g | inner ℝ u g = 0} = 0 := by
  haveI : NullSingletonClass (gaussianReal (0:ℝ) 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  have hm : Measurable (fun g : E => inner ℝ u g) := by fun_prop
  have hset : {g : E | inner ℝ u g = 0} = (fun g => inner ℝ u g) ⁻¹' ({0} : Set ℝ) := rfl
  rw [hset, ← Measure.map_apply hm (measurableSet_singleton 0), map_inner_stdGaussian u hu]
  exact measure_singleton 0

lemma pair_law (u w : E) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (horth : inner ℝ u w = 0) :
    (stdGaussian E).map (fun g => (inner ℝ u g, inner ℝ w g)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  refine (charFun_eq_prod_iff (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
    (ξ := (stdGaussian E).map (fun g => (inner ℝ u g, inner ℝ w g)))).1 ?_
  intro t
  set t1 := t.ofLp.1 with ht1
  set t2 := t.ofLp.2 with ht2
  have hmap : (Measure.map (WithLp.toLp 2)
      ((stdGaussian E).map (fun g => (inner ℝ u g, inner ℝ w g))))
      = (stdGaussian E).map (fun g => WithLp.toLp 2 (inner ℝ u g, inner ℝ w g)) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hmap]
  have hmeas : Measurable (fun g : E => WithLp.toLp 2 (inner ℝ u g, inner ℝ w g)) := by fun_prop
  rw [charFun_apply, integral_map hmeas.aemeasurable (by fun_prop)]
  have hpt : ∀ g : E, Complex.exp (↑(inner ℝ (WithLp.toLp 2 (inner ℝ u g, inner ℝ w g)) t) * Complex.I)
      = Complex.exp (↑(inner ℝ (t1 • u + t2 • w) g) * Complex.I) := by
    intro g
    have hval : inner ℝ (WithLp.toLp 2 (inner ℝ u g, inner ℝ w g)) t
        = inner ℝ (t1 • u + t2 • w) g := by
      rw [WithLp.prod_inner_apply]
      simp only [WithLp.ofLp_toLp]
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      have hstar : ∀ x : ℝ, starRingEnd ℝ x = x := fun x => rfl
      simp only [RCLike.inner_apply, RCLike.star_def, RingHom.id_apply, Complex.conj_ofReal,
        hstar]
      rw [← ht1, ← ht2]
    rw [hval]
  have hcomm : ∀ x : E, inner ℝ (t1 • u + t2 • w) x = inner ℝ x (t1 • u + t2 • w) :=
    fun x => real_inner_comm _ _
  simp only [hpt, hcomm, ← charFun_apply, charFun_stdGaussian]
  have hnorm : ‖t1 • u + t2 • w‖ ^ 2 = t1 ^ 2 + t2 ^ 2 := by
    rw [norm_add_sq_real]
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hu, hw, mul_one, mul_one,
      real_inner_smul_left, real_inner_smul_right, horth, sq_abs, sq_abs]
    ring
  have hcast : (↑‖t1 • u + t2 • w‖ : ℂ) ^ 2 = (↑t1 : ℂ) ^ 2 + (↑t2 : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, hnorm]
    push_cast
    ring
  rw [hcast, charFun_gaussianReal, charFun_gaussianReal]
  simp only [NNReal.coe_one, Complex.ofReal_one, Complex.ofReal_zero, mul_zero, zero_mul,
    one_mul]
  rw [← Complex.exp_add]
  congr 1
  ring


/-! ### `Real.sign` bookkeeping -/

lemma sign_ne_iff_mul_neg {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (Real.sign x ≠ Real.sign y) ↔ x * y < 0 := by
  constructor
  · intro h
    rcases lt_or_gt_of_ne hx with hx' | hx' <;> rcases lt_or_gt_of_ne hy with hy' | hy'
    · rw [Real.sign_of_neg hx', Real.sign_of_neg hy'] at h
      exact absurd rfl h
    · exact mul_neg_of_neg_of_pos hx' hy'
    · exact mul_neg_of_pos_of_neg hx' hy'
    · rw [Real.sign_of_pos hx', Real.sign_of_pos hy'] at h
      exact absurd rfl h
  · intro h
    rcases lt_or_gt_of_ne hx with hx' | hx' <;> rcases lt_or_gt_of_ne hy with hy' | hy'
    · rw [Real.sign_of_neg hx', Real.sign_of_neg hy']
      exact absurd h (by nlinarith : ¬ (x * y < 0))
    · rw [Real.sign_of_neg hx', Real.sign_of_pos hy']
      nlinarith
    · rw [Real.sign_of_pos hx', Real.sign_of_neg hy']
      nlinarith
    · rw [Real.sign_of_pos hx', Real.sign_of_pos hy']
      exact absurd h (by nlinarith : ¬ (x * y < 0))

/-- Away from the two null hyperplanes, "different signs" is "negative product". -/
lemma indicator_sign_ae (u w : E) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    (fun g : E => if Real.sign (inner ℝ u g) = Real.sign (inner ℝ w g) then (0:ℝ) else 1)
      =ᵐ[stdGaussian E]
    (fun g : E => if inner ℝ u g * inner ℝ w g < 0 then (1:ℝ) else 0) := by
  have hNu := measure_inner_eq_zero u hu
  have hNw := measure_inner_eq_zero w hw
  filter_upwards [compl_mem_ae_iff.2 hNu, compl_mem_ae_iff.2 hNw] with g hgu hgw
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hgu hgw
  by_cases h : inner ℝ u g * inner ℝ w g < 0
  · rw [if_pos h, if_neg (sign_ne_iff_mul_neg hgu hgw |>.2 h)]
  · rw [if_neg h, if_pos]
    by_contra hne
    exact h ((sign_ne_iff_mul_neg hgu hgw).1 hne)

/-- The final arccos bookkeeping. -/
lemma arccos_bookkeeping (t : ℝ) :
    2 * (1 / 4 - Real.arcsin t / (2 * Real.pi)) = Real.arccos t / Real.pi := by
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-! ### Per-edge reduction -/

/-- Per-edge statement, in the "quadrant" form. -/
def QuadHyp (D : ℕ) : Prop :=
  ∀ (u w : EuclideanSpace ℝ (Fin D)), ‖u‖ = 1 → ‖w‖ = 1 →
    ∫ g, (if inner ℝ u g * inner ℝ w g < 0 then (1:ℝ) else 0)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin D)))
      = Real.arccos (inner ℝ u w) / Real.pi

/-- From the quadrant form to the `Real.sign` form of one edge. -/
lemma per_edge_of_quad (u w : E) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hquad : ∫ g, (if inner ℝ u g * inner ℝ w g < 0 then (1:ℝ) else 0)
        ∂(stdGaussian E) = Real.arccos (inner ℝ u w) / Real.pi) :
    ∫ g, (if Real.sign (inner ℝ u g) = Real.sign (inner ℝ w g) then (0:ℝ) else 1)
        ∂(stdGaussian E) = Real.arccos (inner ℝ u w) / Real.pi := by
  rw [integral_congr_ae (indicator_sign_ae u w hu hw), hquad]



lemma eq_of_inner_eq_one {u w : E} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (h : inner ℝ u w = 1) :
    w = u := by
  have hcomm : inner ℝ w u = 1 := by rw [real_inner_comm, h]
  have h1 : ‖w - u‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, hu, hw, hcomm]
    norm_num
  have h2 : ‖w - u‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1
  exact sub_eq_zero.1 (norm_eq_zero.1 h2)

lemma eq_neg_of_inner_eq_neg_one {u w : E} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (h : inner ℝ u w = -1) : w = -u := by
  have hcomm : inner ℝ w u = -1 := by rw [real_inner_comm, h]
  have h1 : ‖w + u‖ ^ 2 = 0 := by
    rw [norm_add_sq_real, hu, hw, hcomm]
    norm_num
  have h2 : ‖w + u‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1
  exact eq_neg_of_add_eq_zero_left (norm_eq_zero.1 h2)

lemma quad_one (u w : E) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (h : inner ℝ u w = 1) :
    ∫ g, (if inner ℝ u g * inner ℝ w g < 0 then (1:ℝ) else 0) ∂(stdGaussian E)
      = Real.arccos (inner ℝ u w) / Real.pi := by
  have hwu : w = u := eq_of_inner_eq_one hu hw h
  have hzero : (fun g : E => (if inner ℝ u g * inner ℝ u g < 0 then (1:ℝ) else 0)) = fun _ => 0 := by
    funext g
    rw [if_neg (by nlinarith [sq_nonneg (inner ℝ u g)] : ¬ (inner ℝ u g * inner ℝ u g < 0))]
  have huu : inner ℝ u u = 1 := by simpa [hwu] using h
  rw [hwu, huu, Real.arccos_one, zero_div, hzero, integral_zero]

lemma quad_neg_one (u w : E) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (h : inner ℝ u w = -1) :
    ∫ g, (if inner ℝ u g * inner ℝ w g < 0 then (1:ℝ) else 0) ∂(stdGaussian E)
      = Real.arccos (inner ℝ u w) / Real.pi := by
  have hwu : w = -u := eq_neg_of_inner_eq_neg_one hu hw h
  have hN := measure_inner_eq_zero u hu
  have hcongr : (fun g : E => (if inner ℝ u g * inner ℝ w g < 0 then (1:ℝ) else 0))
      =ᵐ[stdGaussian E] (fun _ => 1) := by
    filter_upwards [compl_mem_ae_iff.2 hN] with g hg
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hg
    rw [hwu, inner_neg_left]
    have hx : inner ℝ u g ≠ 0 := hg
    rw [if_pos (by nlinarith [mul_self_pos.mpr hx] : inner ℝ u g * -inner ℝ u g < 0)]
  rw [integral_congr_ae hcongr, integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  rw [h, Real.arccos_neg_one, div_self Real.pi_ne_zero]


/-- The minimal remaining gap: the quadrant form only in the non-degenerate case `|t| < 1`. -/
def NondegQuad (D : ℕ) : Prop :=
  ∀ (u w : EuclideanSpace ℝ (Fin D)), ‖u‖ = 1 → ‖w‖ = 1 →
    -1 < inner ℝ u w → inner ℝ u w < 1 →
    ∫ g, (if inner ℝ u g * inner ℝ w g < 0 then (1:ℝ) else 0)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin D)))
      = Real.arccos (inner ℝ u w) / Real.pi

/-- `NondegQuad` implies `QuadHyp`: the endpoints `⟪u,w⟫ = ±1` are handled. -/
lemma quadHyp_of_nondeg {D : ℕ} (h : NondegQuad D) : QuadHyp D := by
  intro u w hu hw
  rcases lt_trichotomy (inner ℝ u w) 1 with h1 | h1 | h1
  · rcases lt_trichotomy (inner ℝ u w) (-1) with h2 | h2 | h2
    · -- impossible: ⟪u,w⟫ < -1 contradicts Cauchy–Schwarz
      have hcw : |inner ℝ u w| ≤ ‖u‖ * ‖w‖ := abs_real_inner_le_norm u w
      rw [hu, hw, one_mul] at hcw
      linarith [neg_abs_le (inner ℝ u w)]
    · exact quad_neg_one u w hu hw h2
    · exact h u w hu hw h2 h1
  · exact quad_one u w hu hw h1
  · -- impossible: 1 < ⟪u,w⟫ contradicts Cauchy–Schwarz
    have hcw : |inner ℝ u w| ≤ ‖u‖ * ‖w‖ := abs_real_inner_le_norm u w
    rw [hu, hw, one_mul] at hcw
    linarith [le_abs_self (inner ℝ u w)]

end GWa

open GWa

theorem gw_rounding_expectation_of_quad (D : ℕ) (hq : QuadHyp D) (G : Input)
    (v : Fin G.n → EuclideanSpace ℝ (Fin D)) (hunit : ∀ i, ‖v i‖ = 1) :
    ∫ g : EuclideanSpace ℝ (Fin D),
        (∑ e : Edge G.n, (G.weights e : ℝ) *
          (if Real.sign (inner ℝ (v e.val.1) g) = Real.sign (inner ℝ (v e.val.2) g) then 0 else 1))
      ∂(stdGaussian (EuclideanSpace ℝ (Fin D))) =
    ∑ e : Edge G.n, (G.weights e : ℝ) * Real.arccos (inner ℝ (v e.val.1) (v e.val.2)) / Real.pi := by
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl ?_
    intro e _
    rw [integral_const_mul]
    rw [per_edge_of_quad (v e.val.1) (v e.val.2) (hunit _) (hunit _)
      (hq (v e.val.1) (v e.val.2) (hunit _) (hunit _))]
    ring
  · intro e _
    have hc : (0:ℝ) ≤ (G.weights e : ℝ) := by
      have := (G.weights e).2
      exact_mod_cast this
    refine Integrable.of_bound ?_ (G.weights e : ℝ) ?_
    · exact (measurable_indicator_sign (v e.val.1) (v e.val.2)).aestronglyMeasurable.const_mul _
    · filter_upwards with g
      have h1 : ‖(if Real.sign (inner ℝ (v e.val.1) g) = Real.sign (inner ℝ (v e.val.2) g)
          then (0:ℝ) else 1)‖ ≤ 1 := by
        split_ifs <;> simp
      rw [norm_mul, Real.norm_of_nonneg hc]
      nlinarith

theorem gw_rounding_expectation_of_nondeg (D : ℕ) (hq : NondegQuad D) (G : Input)
    (v : Fin G.n → EuclideanSpace ℝ (Fin D)) (hunit : ∀ i, ‖v i‖ = 1) :
    ∫ g : EuclideanSpace ℝ (Fin D),
        (∑ e : Edge G.n, (G.weights e : ℝ) *
          (if Real.sign (inner ℝ (v e.val.1) g) = Real.sign (inner ℝ (v e.val.2) g) then 0 else 1))
      ∂(stdGaussian (EuclideanSpace ℝ (Fin D))) =
    ∑ e : Edge G.n, (G.weights e : ℝ) * Real.arccos (inner ℝ (v e.val.1) (v e.val.2)) / Real.pi :=
  gw_rounding_expectation_of_quad D (quadHyp_of_nondeg hq) G v hunit

end QuantumMaxCutEnergy


open MeasureTheory Set Real Filter
open scoped Topology

/-! ## Auxiliary one-variable integrals -/

private lemma integral_Ioi_exp_neg_mul {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi (0:ℝ), Real.exp (-(b * x)) = 1 / b := by
  have h := integral_comp_mul_left_Ioi (fun y : ℝ => Real.exp (-y)) (0:ℝ) hb
  rw [h, mul_zero, integral_exp_neg_Ioi, neg_zero, Real.exp_zero, smul_eq_mul, mul_one,
    one_div]

private lemma integral_Ioi_mul_exp_neg_mul_sq {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi (0:ℝ), x * Real.exp (-(a * x ^ 2)) = 1 / (2 * a) := by
  have hA1 := integral_Ioi_exp_neg_mul ha
  have h := integral_comp_rpow_Ioi (fun y : ℝ => Real.exp (-(a * y))) (p := 2) (by norm_num)
  rw [hA1] at h
  have key : ∫ x in Ioi (0:ℝ), (2 * (x * Real.exp (-(a * x ^ 2)))) = 1 / a := by
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have h1 : (2:ℝ) - 1 = 1 := by norm_num
    simp only [h1, Real.rpow_one, Real.rpow_two, smul_eq_mul,
      abs_of_pos (by norm_num : (0:ℝ) < 2)]
    ring
  have key2 : 2 * (∫ x in Ioi (0:ℝ), x * Real.exp (-(a * x ^ 2))) = 1 / a := by
    rw [← integral_const_mul]
    exact key
  have hstep : (∫ x in Ioi (0:ℝ), x * Real.exp (-(a * x ^ 2))) = (1 / a) / 2 := by
    rw [eq_div_iff (by norm_num : (2:ℝ) ≠ 0)]
    linarith
  rw [hstep]
  have ha' : a ≠ 0 := ha.ne'
  field_simp

/-! ## The arctan-type integral `∫_0^∞ du / ((u-t)^2+s^2)` -/

private lemma arctan_data {t s : ℝ} (hs : 0 < s) :
    (∀ u ∈ Ioi (0:ℝ),
        HasDerivAt (fun u : ℝ => (1 / s) * Real.arctan ((u - t) / s))
          (((u - t) ^ 2 + s ^ 2)⁻¹) u) ∧
    ContinuousWithinAt (fun u : ℝ => (1 / s) * Real.arctan ((u - t) / s)) (Ici 0) 0 ∧
    (∀ u ∈ Ioi (0:ℝ), 0 ≤ ((u - t) ^ 2 + s ^ 2)⁻¹) ∧
    Tendsto (fun u : ℝ => (1 / s) * Real.arctan ((u - t) / s)) atTop (𝓝 ((1/s) * (π/2))) := by
  have hderiv : ∀ u ∈ Ioi (0:ℝ),
      HasDerivAt (fun u : ℝ => (1 / s) * Real.arctan ((u - t) / s))
        (((u - t) ^ 2 + s ^ 2)⁻¹) u := by
    intro u _
    have hid : HasDerivAt (fun u : ℝ => u - t) 1 u := by
      simpa using (hasDerivAt_id u).sub_const t
    have h1 : HasDerivAt (fun u : ℝ => (u - t) / s) (1 / s) u := by
      simpa using hid.div_const s
    have h3 := HasDerivAt.arctan (f := fun u : ℝ => (u - t) / s) (x := u) (f' := 1 / s) h1
    have h4 := h3.const_mul (1 / s)
    refine h4.congr_deriv ?_
    have hne : ((u - t) ^ 2 + s ^ 2) ≠ 0 := by positivity
    field_simp
    ring
  have hcont : ContinuousWithinAt (fun u : ℝ => (1 / s) * Real.arctan ((u - t) / s)) (Ici 0) 0 := by
    apply Continuous.continuousWithinAt; fun_prop
  have hpos : ∀ u ∈ Ioi (0:ℝ), 0 ≤ ((u - t) ^ 2 + s ^ 2)⁻¹ := by
    intro u _; positivity
  have hlim : Tendsto (fun u : ℝ => (1 / s) * Real.arctan ((u - t) / s)) atTop
      (𝓝 ((1/s) * (π/2))) := by
    have h1 : Tendsto (fun u : ℝ => u - t) atTop atTop :=
      tendsto_atTop_add_const_right atTop (-t) (tendsto_id (α := ℝ))
    have h2 : Tendsto (fun u : ℝ => (u - t) / s) atTop atTop := h1.atTop_div_const hs
    have h3 : Tendsto (fun u : ℝ => Real.arctan ((u - t) / s)) atTop (𝓝 (π/2)) :=
      (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp h2
    exact h3.const_mul (1/s)
  exact ⟨hderiv, hcont, hpos, hlim⟩

private lemma integral_Ioi_inv_sq_add {t s : ℝ} (hs : 0 < s) :
    ∫ u in Ioi (0:ℝ), ((u - t) ^ 2 + s ^ 2)⁻¹ = (π / 2 + Real.arctan (t / s)) / s := by
  obtain ⟨hderiv, hcont, hpos, hlim⟩ := arctan_data (t := t) hs
  have hmain := integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos hlim
  rw [hmain]
  simp only [zero_sub, neg_div, arctan_neg]
  have hs' : s ≠ 0 := hs.ne'
  field_simp
  ring

private lemma integrableOn_Ioi_inv_sq_add {t s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u : ℝ => ((u - t) ^ 2 + s ^ 2)⁻¹) (Ioi 0) := by
  obtain ⟨hderiv, hcont, hpos, hlim⟩ := arctan_data (t := t) hs
  exact integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos hlim

/-! ## The bivariate normal quadrant formula -/

theorem bivariate_normal_quadrant (t : ℝ) (ht1 : -1 < t) (ht2 : t < 1) :
    ∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
        (1 / (2 * Real.pi * Real.sqrt (1 - t ^ 2))) *
          Real.exp (-(x ^ 2 - 2 * t * x * y + y ^ 2) / (2 * (1 - t ^ 2)))
      = 1 / 4 + Real.arcsin t / (2 * Real.pi) := by
  have hS : (0:ℝ) < 1 - t ^ 2 := by
    nlinarith [mul_pos (by linarith : (0:ℝ) < 1 + t) (by linarith : (0:ℝ) < 1 - t)]
  set s : ℝ := Real.sqrt (1 - t ^ 2) with hsdef
  have hs : (0:ℝ) < s := by rw [hsdef]; exact Real.sqrt_pos.2 hS
  have hs2 : s ^ 2 = 1 - t ^ 2 := by rw [hsdef]; exact Real.sq_sqrt hS.le
  set c : ℝ := 1 / (2 * Real.pi * s) with hc
  have hcpos : (0:ℝ) < c := by rw [hc]; positivity
  set A : ℝ → ℝ := fun u => 1 - 2 * t * u + u ^ 2 with hA
  have hAeq : ∀ u : ℝ, A u = (u - t) ^ 2 + (1 - t ^ 2) := by intro u; rw [hA]; ring
  have hApos : ∀ u : ℝ, 0 < A u := by
    intro u; rw [hAeq u]; nlinarith [sq_nonneg (u - t), hS]
  set G : ℝ → ℝ → ℝ :=
    fun x u => c * (x * Real.exp (-(x ^ 2 * A u) / (2 * (1 - t ^ 2)))) with hG
  -- STEP 1: dilation `y = x * u` in the inner integral
  have hstep1 : ∀ x ∈ Ioi (0:ℝ),
      (∫ y in Ioi (0:ℝ),
        c * Real.exp (-(x ^ 2 - 2 * t * x * y + y ^ 2) / (2 * (1 - t ^ 2))))
      = ∫ u in Ioi (0:ℝ),
          x * (c * Real.exp (-(x ^ 2 - 2 * t * x * (x * u) + (x * u) ^ 2) /
            (2 * (1 - t ^ 2)))) := by
    intro x hx
    have hx0 : 0 < x := hx
    have h := integral_comp_mul_left_Ioi
      (fun y : ℝ => c * Real.exp (-(x ^ 2 - 2 * t * x * y + y ^ 2) / (2 * (1 - t ^ 2))))
      (0:ℝ) hx0
    simp only [mul_zero] at h
    rw [show (∫ u in Ioi (0:ℝ), x * (c * Real.exp (-(x ^ 2 - 2 * t * x * (x * u) + (x * u) ^ 2) / (2 * (1 - t ^ 2)))))
        = x * ∫ u in Ioi (0:ℝ), (c * Real.exp (-(x ^ 2 - 2 * t * x * (x * u) + (x * u) ^ 2) / (2 * (1 - t ^ 2)))) from integral_const_mul x _]
    rw [h]
    simp only [smul_eq_mul]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hstep1]
  -- STEP 2: identify the integrand with `G`
  have hstep2 : ∀ x ∈ Ioi (0:ℝ),
      (∫ u in Ioi (0:ℝ),
          x * (c * Real.exp (-(x ^ 2 - 2 * t * x * (x * u) + (x * u) ^ 2) /
            (2 * (1 - t ^ 2)))))
      = ∫ u in Ioi (0:ℝ), G x u := by
    intro x _
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    have hexp : x ^ 2 - 2 * t * x * (x * u) + (x * u) ^ 2 = x ^ 2 * A u := by
      rw [hA]; ring
    simp only [hG, hexp]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hstep2]
  -- STEP 3: evaluate the inner `x`-integral for fixed `u`
  have hInner : ∀ u ∈ Ioi (0:ℝ), (∫ x in Ioi (0:ℝ), G x u)
      = c * (1 - t ^ 2) * ((u - t) ^ 2 + (1 - t ^ 2))⁻¹ := by
    intro u _
    have hApos' : 0 < A u / (2 * (1 - t ^ 2)) := div_pos (hApos u) (by linarith)
    have h1 : ∫ x in Ioi (0:ℝ), x * Real.exp (-(A u / (2 * (1 - t ^ 2)) * x ^ 2))
        = 1 / (2 * (A u / (2 * (1 - t ^ 2)))) := integral_Ioi_mul_exp_neg_mul_sq hApos'
    have hsplit : ∫ x in Ioi (0:ℝ), G x u
        = c * ∫ x in Ioi (0:ℝ), x * Real.exp (-(x ^ 2 * A u) / (2 * (1 - t ^ 2))) := by
      simp only [hG]
      rw [integral_const_mul]
    have h2 : ∫ x in Ioi (0:ℝ), G x u
        = c * ∫ x in Ioi (0:ℝ), x * Real.exp (-(A u / (2 * (1 - t ^ 2)) * x ^ 2)) := by
      rw [hsplit]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      have h3 : -(x ^ 2 * A u) / (2 * (1 - t ^ 2))
          = -(A u / (2 * (1 - t ^ 2)) * x ^ 2) := by
        field_simp
      rw [h3]
    rw [h2, h1, hAeq u]
    have hne : ((u - t) ^ 2 + (1 - t ^ 2)) ≠ 0 := by nlinarith [sq_nonneg (u - t), hS]
    have hS' : (1 - t ^ 2) ≠ 0 := hS.ne'
    field_simp
  -- STEP 4: Tonelli
  have hmeas : AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    apply Measurable.aestronglyMeasurable
    simp only [hG, hA]
    fun_prop
  have hInt : Integrable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards with u
      have ha : 0 < A u / (2 * (1 - t ^ 2)) := div_pos (hApos u) (by linarith)
      have h1c : Integrable
          (fun x : ℝ => x * Real.exp (-(A u / (2 * (1 - t ^ 2))) * x ^ 2)) :=
        integrable_mul_exp_neg_mul_sq ha
      have h1 : Integrable
          (fun x : ℝ => x * Real.exp (-(A u / (2 * (1 - t ^ 2)) * x ^ 2))) := by
        refine Integrable.congr h1c ?_
        filter_upwards with x
        have h4 : -(A u / (2 * (1 - t ^ 2))) * x ^ 2
            = -(A u / (2 * (1 - t ^ 2)) * x ^ 2) := by ring
        rw [h4]
      have h2 : Integrable
          (fun x : ℝ => c * (x * Real.exp (-(x ^ 2 * A u) / (2 * (1 - t ^ 2))))) := by
        refine Integrable.congr (h1.const_mul c) ?_
        filter_upwards with x
        have h3 : -(x ^ 2 * A u) / (2 * (1 - t ^ 2))
            = -(A u / (2 * (1 - t ^ 2)) * x ^ 2) := by
          field_simp
        rw [h3]
      exact h2.integrableOn
    · have hbase : IntegrableOn
          (fun u : ℝ => c * (1 - t ^ 2) * ((u - t) ^ 2 + (1 - t ^ 2))⁻¹) (Ioi 0) := by
        have h := (integrableOn_Ioi_inv_sq_add (t := t) (s := s) hs).const_mul (c * (1 - t ^ 2))
        rw [hs2] at h
        exact h
      refine Integrable.congr hbase ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hnorm : ∀ x ∈ Ioi (0:ℝ), ‖Function.uncurry G (x,u)‖ = G x u := by
        intro x hx
        have hx0 : 0 < x := hx
        have hpos : 0 < G x u := by
          rw [hG]
          have hexp : 0 < Real.exp (-(x ^ 2 * A u) / (2 * (1 - t ^ 2))) := Real.exp_pos _
          positivity
        simp only [Function.uncurry_apply_pair, Real.norm_eq_abs]
        exact abs_of_pos hpos
      rw [setIntegral_congr_fun measurableSet_Ioi hnorm, hInner u hu]
  rw [integral_integral_swap hInt]
  rw [setIntegral_congr_fun measurableSet_Ioi hInner]
  rw [integral_const_mul]
  -- STEP 5: the remaining one-variable integral and the final arithmetic
  have hB := integral_Ioi_inv_sq_add (t := t) (s := s) hs
  have harc : Real.arctan (t / s) = Real.arcsin t := by
    rw [hsdef]
    exact (Real.arcsin_eq_arctan ⟨ht1, ht2⟩).symm
  rw [← hs2]
  rw [hB, harc]
  rw [hc]
  field_simp
  ring


open MeasureTheory Set Real Filter ProbabilityTheory
open scoped Topology RealInnerProductSpace NNReal

namespace GW

variable {D : ℕ}

def ssq (s : ℝ) : ℝ≥0 := ⟨s ^ 2, sq_nonneg s⟩

@[simp] lemma ssq_coe (s : ℝ) : ((ssq s : ℝ≥0) : ℝ) = s ^ 2 := rfl

lemma ssq_ne_zero {s : ℝ} (hs : 0 < s) : ssq s ≠ 0 := by
  have h : ((ssq s : ℝ≥0) : ℝ) ≠ 0 := by simp [hs.ne']
  intro hh
  exact h (by rw [hh]; simp)

lemma gaussianPDFReal_neg_arg (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal m v (-x) = gaussianPDFReal (-m) v x := by
  simp only [gaussianPDFReal]
  rw [show -x - m = -(x + m) by ring, show x - -m = x + m by ring, neg_sq]

/-- The correlated bivariate normal density (with off-diagonal parameter `t`). -/
noncomputable def R (t s : ℝ) (x y : ℝ) : ℝ :=
  gaussianPDFReal 0 1 x * gaussianPDFReal (t * x) (ssq s) y

lemma R_nonneg (t s x y : ℝ) : 0 ≤ R t s x y :=
  mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)

lemma R_flip (t s x y : ℝ) : R t s (-x) (-y) = R t s x y := by
  simp only [R, gaussianPDFReal_neg_arg, mul_neg, neg_neg, show gaussianPDFReal 0 1 (-x) = gaussianPDFReal 0 1 x by
    simp [gaussianPDFReal, sq]]

lemma R_flip_y {t s : ℝ} (x y : ℝ) : R t s x (-y) = R (-t) s x y := by
  simp only [R, gaussianPDFReal_neg_arg, neg_mul]

lemma R_flip_x {t s : ℝ} (x y : ℝ) : R t s (-x) y = R (-t) s x y := by
  simp only [R, mul_neg, gaussianPDFReal_neg_arg,
    show gaussianPDFReal 0 1 (-x) = gaussianPDFReal 0 1 x by simp [gaussianPDFReal, sq]]
  congr 2
  ring

lemma integrable_R_slice {t s : ℝ} (x : ℝ) : Integrable (fun y => R t s x y) := by
  have h1 : Integrable (fun y : ℝ => gaussianPDFReal (t * x) (ssq s) y) :=
    integrable_gaussianPDFReal _ _
  exact h1.const_mul _

lemma integral_R_slice {t s : ℝ} (hs : 0 < s) (x : ℝ) : ∫ y, R t s x y = gaussianPDFReal 0 1 x := by
  have h1 : ∀ y : ℝ, R t s x y = gaussianPDFReal 0 1 x * gaussianPDFReal (t * x) (ssq s) y := fun y => rfl
  simp only [h1, integral_const_mul, smul_eq_mul,
    integral_gaussianPDFReal_eq_one (t * x) (ssq_ne_zero hs), mul_one]

/-- half-line integrals of a slice are bounded by the total mass -/
lemma setIntegral_Iio_R_le {t s : ℝ} (hs : 0 < s) (x c : ℝ) :
    ∫ y in Iio c, R t s x y ≤ gaussianPDFReal 0 1 x := by
  rw [← integral_R_slice hs x]
  exact setIntegral_le_integral (integrable_R_slice x) (ae_of_all _ fun y => R_nonneg t s x y)

lemma setIntegral_Ioi_R_le {t s : ℝ} (hs : 0 < s) (x c : ℝ) :
    ∫ y in Ioi c, R t s x y ≤ gaussianPDFReal 0 1 x := by
  rw [← integral_R_slice hs x]
  exact setIntegral_le_integral (integrable_R_slice x) (ae_of_all _ fun y => R_nonneg t s x y)

lemma measurable_slice_Iio (t s c : ℝ) : Measurable (fun x => ∫ y in Iio c, R t s x y) := by
  classical
  have h1 : Measurable (fun p : ℝ × ℝ => R t s p.1 p.2) := by
    simp only [R, gaussianPDFReal]
    fun_prop
  have hset : MeasurableSet {p : ℝ × ℝ | p.2 < c} := measurableSet_Iio.preimage measurable_snd
  have hR : StronglyMeasurable (fun p : ℝ × ℝ => if p.2 < c then R t s p.1 p.2 else 0) := by
    have hite : Measurable (fun p : ℝ × ℝ => if p.2 < c then R t s p.1 p.2 else 0) :=
      Measurable.ite hset h1 (measurable_const : Measurable fun _ : ℝ × ℝ => (0:ℝ))
    exact hite.stronglyMeasurable
  have h3 := StronglyMeasurable.integral_prod_right (ν := volume)
    (f := fun (x : ℝ) (y : ℝ) => if y < c then R t s x y else 0) hR
  have heq : (fun x => ∫ y in Iio c, R t s x y)
      = (fun x => ∫ y, if y < c then R t s x y else 0) := by
    funext x
    rw [← integral_indicator measurableSet_Iio]
    simp only [Set.indicator_apply, Set.mem_Iio]
  rw [heq]
  exact h3.measurable

lemma measurable_slice_Ioi (t s c : ℝ) : Measurable (fun x => ∫ y in Ioi c, R t s x y) := by
  classical
  have h1 : Measurable (fun p : ℝ × ℝ => R t s p.1 p.2) := by
    simp only [R, gaussianPDFReal]
    fun_prop
  have hset : MeasurableSet {p : ℝ × ℝ | c < p.2} := measurableSet_Ioi.preimage measurable_snd
  have hR : StronglyMeasurable (fun p : ℝ × ℝ => if c < p.2 then R t s p.1 p.2 else 0) := by
    have hite : Measurable (fun p : ℝ × ℝ => if c < p.2 then R t s p.1 p.2 else 0) :=
      Measurable.ite hset h1 (measurable_const : Measurable fun _ : ℝ × ℝ => (0:ℝ))
    exact hite.stronglyMeasurable
  have h3 := StronglyMeasurable.integral_prod_right (ν := volume)
    (f := fun (x : ℝ) (y : ℝ) => if c < y then R t s x y else 0) hR
  have heq : (fun x => ∫ y in Ioi c, R t s x y)
      = (fun x => ∫ y, if c < y then R t s x y else 0) := by
    funext x
    rw [← integral_indicator measurableSet_Ioi]
    simp only [Set.indicator_apply, Set.mem_Ioi]
  rw [heq]
  exact h3.measurable

lemma integrable_outer_pos {t s : ℝ} (hs : 0 < s) :
    Integrable (fun x => if 0 < x then ∫ y in Iio 0, R t s x y else 0) := by
  classical
  have hbase : Integrable (fun x : ℝ => |gaussianPDFReal 0 1 x|) :=
    (integrable_gaussianPDFReal 0 1).abs
  refine Integrable.mono' hbase ?_ ?_
  · exact (Measurable.ite measurableSet_Ioi (measurable_slice_Iio t s 0) measurable_const).aestronglyMeasurable
  · filter_upwards with x
    by_cases hx : 0 < x
    · simp only [hx, if_true]
      have h0 : 0 ≤ ∫ y in Iio 0, R t s x y :=
        setIntegral_nonneg measurableSet_Iio (fun y _ => R_nonneg t s x y)
      have h1 : ∫ y in Iio 0, R t s x y ≤ gaussianPDFReal 0 1 x :=
        setIntegral_Iio_R_le (t := t) (s := s) hs x 0
      calc ‖∫ y in Iio 0, R t s x y‖ = ∫ y in Iio 0, R t s x y := by
            rw [Real.norm_eq_abs, abs_of_nonneg h0]
        _ ≤ gaussianPDFReal 0 1 x := h1
        _ ≤ |gaussianPDFReal 0 1 x| := le_abs_self _
    · simp [hx]

lemma integrable_outer_neg {t s : ℝ} (hs : 0 < s) :
    Integrable (fun x => if x < 0 then ∫ y in Ioi 0, R t s x y else 0) := by
  classical
  have hbase : Integrable (fun x : ℝ => |gaussianPDFReal 0 1 x|) :=
    (integrable_gaussianPDFReal 0 1).abs
  refine Integrable.mono' hbase ?_ ?_
  · exact (Measurable.ite measurableSet_Iio (measurable_slice_Ioi t s 0) measurable_const).aestronglyMeasurable
  · filter_upwards with x
    by_cases hx : x < 0
    · simp only [hx, if_true]
      have h0 : 0 ≤ ∫ y in Ioi 0, R t s x y :=
        setIntegral_nonneg measurableSet_Ioi (fun y _ => R_nonneg t s x y)
      have h1 : ∫ y in Ioi 0, R t s x y ≤ gaussianPDFReal 0 1 x :=
        setIntegral_Ioi_R_le (t := t) (s := s) hs x 0
      calc ‖∫ y in Ioi 0, R t s x y‖ = ∫ y in Ioi 0, R t s x y := by
            rw [Real.norm_eq_abs, abs_of_nonneg h0]
        _ ≤ gaussianPDFReal 0 1 x := h1
        _ ≤ |gaussianPDFReal 0 1 x| := le_abs_self _
    · simp [hx]

lemma gauss_prod_eq {t s e : ℝ} (hs : 0 < s) (hs2 : s ^ 2 = 1 - t ^ 2) (he : e ^ 2 = t ^ 2)
    (x y : ℝ) :
    gaussianPDFReal 0 1 x * gaussianPDFReal (e * x) (ssq s) y
      = (1 / (2 * Real.pi * s)) *
        Real.exp (-(x ^ 2 - 2 * e * x * y + y ^ 2) / (2 * (1 - e ^ 2))) := by
  have hs2' : (1 : ℝ) - e ^ 2 = s ^ 2 := by rw [he, ← hs2]
  have hsqrt : Real.sqrt (2 * Real.pi * s ^ 2) = s * Real.sqrt (2 * Real.pi) := by
    rw [show 2 * Real.pi * s ^ 2 = s ^ 2 * (2 * Real.pi) by ring, Real.sqrt_mul (sq_nonneg s),
      Real.sqrt_sq hs.le]
  have hcoef : (Real.sqrt (2 * Real.pi))⁻¹ * (s * Real.sqrt (2 * Real.pi))⁻¹
      = 1 / (2 * Real.pi * s) := by
    have h : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
    field_simp
    linarith
  have hexp : -x ^ 2 / 2 + -(y - e * x) ^ 2 / (2 * s ^ 2)
      = -(x ^ 2 - 2 * e * x * y + y ^ 2) / (2 * (1 - e ^ 2)) := by
    rw [hs2']
    field_simp
    nlinarith [he]
  have hsq' : ((ssq s : ℝ≥0) : ℝ) = s ^ 2 := rfl
  have hsq1 : ((1 : ℝ≥0) : ℝ) = 1 := by norm_num
  simp only [gaussianPDFReal_def, hsq1, hsq', hsqrt, mul_one, sub_zero]
  rw [show (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) *
      ((s * Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y - e * x) ^ 2 / (2 * s ^ 2)))
      = ((Real.sqrt (2 * Real.pi))⁻¹ * (s * Real.sqrt (2 * Real.pi))⁻¹) *
        (Real.exp (-x ^ 2 / 2) * Real.exp (-(y - e * x) ^ 2 / (2 * s ^ 2))) by ring]
  rw [hcoef, ← Real.exp_add, hexp]

lemma gauss_prod_skew {t s : ℝ} (hs : 0 < s) (x y : ℝ) :
    gaussianPDFReal 0 1 x * gaussianPDFReal 0 1 ((y - t * x) / s)
      = s * (gaussianPDFReal 0 1 x * gaussianPDFReal (t * x) (ssq s) y) := by
  have h1 : (y - t * x) / s = s⁻¹ * (y - t * x) := by field_simp
  rw [h1, gaussianPDFReal_inv_mul hs.ne', abs_of_pos hs]
  simp only [mul_zero, mul_one, gaussianPDFReal_sub, zero_add]
  rw [show NNReal.mk (s ^ 2) (sq_nonneg s) = ssq s from rfl]
  ring

lemma inner_skew_subst (t s a : ℝ) (hs : 0 < s) (F : ℝ → ℝ) :
    ∫ z, F (t * a + s * z) * gaussianPDFReal 0 1 z
      = s⁻¹ * ∫ y, F y * gaussianPDFReal 0 1 ((y - t * a) / s) := by
  have hsne : s ≠ 0 := hs.ne'
  set G : ℝ → ℝ := fun u => F (u + t * a) * gaussianPDFReal 0 1 (u / s) with hGdef
  have h1 : ∫ z, F (t * a + s * z) * gaussianPDFReal 0 1 z = ∫ z, G (s * z) := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hGdef, show t * a + s * z = s * z + t * a by ring,
      show s * z / s = z by field_simp]
  have h2 : ∫ y, G y = ∫ y, F y * gaussianPDFReal 0 1 ((y - t * a) / s) := by
    rw [hGdef]
    have hpt : ∀ y : ℝ, F (y + t * a) * gaussianPDFReal 0 1 (y / s)
        = (fun v => F v * gaussianPDFReal 0 1 ((v - t * a) / s)) (y + t * a) := by
      intro y
      simp only [show y + t * a - t * a = y by ring]
    rw [funext hpt]
    exact integral_add_right_eq_self (fun v => F v * gaussianPDFReal 0 1 ((v - t * a) / s)) (t * a)
  rw [h1, Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hs), smul_eq_mul, h2]

lemma setIntegral_neg_Iio (f : ℝ → ℝ) :
    ∫ y in Set.Iio (0:ℝ), f y = ∫ y in Set.Ioi (0:ℝ), f (-y) := by
  rw [← integral_Iic_eq_integral_Iio (f := f) (x := (0:ℝ))]
  simpa using integral_comp_neg_Iic (c := (0:ℝ)) (f := fun y => f (-y))


lemma ae_ne_zero : (∀ᵐ y : ℝ ∂volume, y ≠ 0) := by
  rw [MeasureTheory.ae_iff]
  simpa using Real.volume_singleton (a := (0:ℝ))

lemma integral_R_quadrant {t s e : ℝ} (hs : 0 < s) (hs2 : s ^ 2 = 1 - t ^ 2) (he : e ^ 2 = t ^ 2)
    (he1 : -1 < e) (he2 : e < 1) :
    ∫ x in Ioi 0, ∫ y in Ioi 0, R e s x y = 1 / 4 + Real.arcsin e / (2 * Real.pi) := by
  have hsq : Real.sqrt (1 - e ^ 2) = s := by
    rw [show 1 - e ^ 2 = s ^ 2 by rw [he, ← hs2]]
    exact Real.sqrt_sq hs.le
  rw [← bivariate_normal_quadrant e he1 he2, hsq]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  simp only [R]
  exact gauss_prod_eq hs hs2 he x y

end GW

namespace OracleGW

variable {D : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin D)

/-- The law of one unit projection under `stdGaussian` is `gaussianReal 0 1`. -/
theorem map_innerSL_stdGaussian (u : E) (hu : ‖u‖ = 1) :
    (stdGaussian E).map (innerSL ℝ u) = gaussianReal 0 1 := by
  haveI : IsGaussian (stdGaussian E) := inferInstance
  rw [IsGaussian.map_eq_gaussianReal]
  have hmean : ∫ x, innerSL ℝ u x ∂(stdGaussian E) = 0 := integral_strongDual_stdGaussian _
  have hvar : Var[⇑(innerSL ℝ u); stdGaussian E] = (1 : NNReal) := by
    rw [variance_dual_stdGaussian, innerSL_apply_norm, hu]
    norm_num
  rw [hmean, hvar]
  norm_num

/-- Orthonormal unit projections of a standard Gaussian are independent. -/
theorem indepFun_inner (u w : E) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (h : ⟪u, w⟫ = 0) :
    IndepFun (fun g => ⟪u, g⟫) (fun g => ⟪w, g⟫) (stdGaussian E) := by
  haveI : IsGaussian (stdGaussian E) := inferInstance
  have hpair : IsGaussian ((stdGaussian E).map (fun g => (⟪u, g⟫, ⟪w, g⟫))) := by
    have h1 := isGaussian_map_of_measurable (μ := stdGaussian E)
      (L := (innerSL ℝ u).prod (innerSL ℝ w)) (by fun_prop)
    have hcoe : ⇑((innerSL ℝ u).prod (innerSL ℝ w)) = fun g => (⟪u, g⟫, ⟪w, g⟫) := by
      funext g; rw [ContinuousLinearMap.prod_apply]; simp
    rwa [hcoe] at h1
  have hcov : cov[(fun g => ⟪u, g⟫), (fun g => ⟪w, g⟫); stdGaussian E] = 0 := by
    rw [← covarianceBilin_apply_eq_cov (IsGaussian.memLp_two_id (μ := stdGaussian E))]
    rw [covarianceBilin_stdGaussian, innerSL_apply_apply]
    exact h
  exact HasGaussianLaw.indepFun_of_covariance_eq_zero
    (IsGaussian.hasGaussianLaw (P := stdGaussian E)) hcov

/-- The joint law of an orthonormal pair of projections is a product of two `gaussianReal 0 1`. -/
theorem map_pair_eq_prod (u w : E) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (h : ⟪u, w⟫ = 0) :
    (stdGaussian E).map (fun g => (⟪u, g⟫, ⟪w, g⟫))
      = (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  have h1 := (indepFun_iff_map_prod_eq_prod_map_map (μ := stdGaussian E)
    (f := fun g => ⟪u, g⟫) (g := fun g => ⟪w, g⟫) (by fun_prop) (by fun_prop)).1
    (indepFun_inner u w hu hw h)
  have h2 : (stdGaussian E).map (fun g => ⟪u, g⟫) = gaussianReal 0 1 := by
    simpa using map_innerSL_stdGaussian u hu
  have h3 : (stdGaussian E).map (fun g => ⟪w, g⟫) = gaussianReal 0 1 := by
    simpa using map_innerSL_stdGaussian w hw
  rw [h1, h2, h3]

/-- Integral form of the orthonormal-pair law. -/
theorem integral_pair_eq (u w : E) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (h : ⟪u, w⟫ = 0)
    (F : ℝ → ℝ → ℝ)
    (hF : AEStronglyMeasurable (Function.uncurry F) ((gaussianReal 0 1).prod (gaussianReal 0 1)))
    (hint : Integrable (Function.uncurry F) ((gaussianReal 0 1).prod (gaussianReal 0 1))) :
    ∫ g, F (⟪u, g⟫) (⟪w, g⟫) ∂(stdGaussian E)
      = ∫ a, ∫ b, F a b ∂(gaussianReal 0 1) ∂(gaussianReal 0 1) := by
  have hmap := map_pair_eq_prod u w hu hw h
  have hgm : AEStronglyMeasurable (Function.uncurry F)
      (Measure.map (fun g => (⟪u, g⟫, ⟪w, g⟫)) (stdGaussian E)) := by
    rw [hmap]; exact hF
  have hstep : ∫ g, F (⟪u, g⟫) (⟪w, g⟫) ∂(stdGaussian E)
      = ∫ p : ℝ × ℝ, Function.uncurry F p
          ∂(Measure.map (fun g => (⟪u, g⟫, ⟪w, g⟫)) (stdGaussian E)) :=
    (integral_map (φ := fun g => (⟪u, g⟫, ⟪w, g⟫)) (by fun_prop) hgm).symm
  rw [hstep, hmap, integral_prod _ hint]
  simp [Function.uncurry]

end OracleGW
-- ==== m3 glue ====
namespace GWc

open MeasureTheory Set Real Filter ProbabilityTheory
open scoped Topology RealInnerProductSpace NNReal BigOperators

variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

theorem dec_orth (u w : E) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (h1 : -1 < inner ℝ u w) (h2 : inner ℝ u w < 1) :
    ∃ (s : ℝ) (w' : E), 0 < s ∧ s ^ 2 = 1 - inner ℝ u w ^ 2 ∧ inner ℝ u w' = 0 ∧ ‖w'‖ = 1
      ∧ w = (inner ℝ u w) • u + s • w' := by
  have ht2 : inner ℝ u w ^ 2 < 1 := by nlinarith
  have h1t : 0 < 1 - inner ℝ u w ^ 2 := by linarith
  refine ⟨Real.sqrt (1 - inner ℝ u w ^ 2),
    (Real.sqrt (1 - inner ℝ u w ^ 2))⁻¹ • (w - (inner ℝ u w) • u),
    Real.sqrt_pos.2 h1t, Real.sq_sqrt h1t.le, ?_, ?_, ?_⟩
  · rw [inner_smul_right, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu]
    ring
  · have hs : 0 < Real.sqrt (1 - inner ℝ u w ^ 2) := Real.sqrt_pos.2 h1t
    have hs2 : Real.sqrt (1 - inner ℝ u w ^ 2) ^ 2 = 1 - inner ℝ u w ^ 2 := Real.sq_sqrt h1t.le
    have hsq : ‖w - (inner ℝ u w) • u‖ ^ 2 = Real.sqrt (1 - inner ℝ u w ^ 2) ^ 2 := by
      rw [norm_sub_sq_real, hw, hs2]
      have h1' : inner ℝ w ((inner ℝ u w) • u) = inner ℝ u w * inner ℝ u w := by
        rw [real_inner_smul_right, real_inner_comm u w]
      have h2' : ‖(inner ℝ u w) • u‖ ^ 2 = inner ℝ u w ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs]
      rw [h1', h2']
      ring
    have hnorm : ‖w - (inner ℝ u w) • u‖ = Real.sqrt (1 - inner ℝ u w ^ 2) := by
      nlinarith [hsq, norm_nonneg (w - (inner ℝ u w) • u), hs.le]
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hs, hnorm, inv_mul_cancel₀ hs.ne']
  · have hs : 0 < Real.sqrt (1 - inner ℝ u w ^ 2) := Real.sqrt_pos.2 h1t
    rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    abel

/-- Pointwise split of the sign indicator. -/
theorem split_indicator (a y : ℝ) :
    (if a * y < 0 then (1:ℝ) else 0)
      = (if 0 < a ∧ y < 0 then (1:ℝ) else 0) + (if a < 0 ∧ 0 < y then (1:ℝ) else 0) := by
  have key : a * y < 0 ↔ (0 < a ∧ y < 0) ∨ (a < 0 ∧ 0 < y) := mul_neg_iff
  have hdisj : ¬ ((0 < a ∧ y < 0) ∧ (a < 0 ∧ 0 < y)) :=
    fun ⟨⟨h1, _⟩, ⟨h2, _⟩⟩ => lt_asymm h1 h2
  by_cases h1 : 0 < a ∧ y < 0
  · rw [if_pos (key.2 (Or.inl h1)), if_pos h1, if_neg (fun h => hdisj ⟨h1, h⟩)]; ring
  · by_cases h2 : a < 0 ∧ 0 < y
    · rw [if_pos (key.2 (Or.inr h2)), if_neg h1, if_pos h2]; ring
    · rw [if_neg (fun h => (key.1 h).elim h1 h2), if_neg h1, if_neg h2]; ring

/-- The main remaining step: the non-degenerate per-edge quadrant value. -/
theorem nondeg_quad (u w : E) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (h1 : -1 < inner ℝ u w) (h2 : inner ℝ u w < 1) :
    ∫ g, (if inner ℝ u g * inner ℝ w g < 0 then (1:ℝ) else 0) ∂(stdGaussian E)
      = Real.arccos (inner ℝ u w) / Real.pi := by
  obtain ⟨s, w', hs, hs2, horth, hwnorm, hdecomp⟩ := dec_orth u w hu hw h1 h2
  set t := inner ℝ u w with ht
  -- pointwise identity for the second projection
  have hinner : ∀ g : E, inner ℝ w g = t * inner ℝ u g + s * inner ℝ w' g := by
    intro g
    rw [hdecomp, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  -- the 2-D integrand
  set F : ℝ → ℝ → ℝ := fun a b => if a * (t * a + s * b) < 0 then (1:ℝ) else 0 with hF
  have hFmeas : Measurable (Function.uncurry F) := by
    have hset : MeasurableSet {p : ℝ × ℝ | p.1 * (t * p.1 + s * p.2) < 0} :=
      isOpen_lt (by fun_prop) continuous_const |>.measurableSet
    have hfun : Function.uncurry F
        = fun p : ℝ × ℝ => if p.1 * (t * p.1 + s * p.2) < 0 then (1:ℝ) else 0 := rfl
    rw [hfun]
    exact Measurable.ite hset measurable_const measurable_const
  have hFint : Integrable (Function.uncurry F) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    refine Integrable.of_bound hFmeas.aestronglyMeasurable 1 (ae_of_all _ fun p => ?_)
    have hp : Function.uncurry F p
        = (if p.1 * (t * p.1 + s * p.2) < 0 then (1:ℝ) else 0) := rfl
    rw [hp]
    by_cases hc : p.1 * (t * p.1 + s * p.2) < 0
    · rw [if_pos hc]; norm_num
    · rw [if_neg hc]; norm_num
  -- transport to two independent standard Gaussians
  have htrans := OracleGW.integral_pair_eq u w' hu hwnorm horth F
    hFmeas.aestronglyMeasurable hFint
  have hLHS : ∫ g, (if inner ℝ u g * inner ℝ w g < 0 then (1:ℝ) else 0) ∂(stdGaussian E)
      = ∫ g, F (inner ℝ u g) (inner ℝ w' g) ∂(stdGaussian E) := by
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    simp only [hF, hinner g]
  rw [hLHS, htrans]
  -- convert the two γ-integrals into Lebesgue integrals against the density
  set φ : ℝ → ℝ := fun x => gaussianPDFReal 0 1 x with hφ
  have hγ1 : ∀ a : ℝ, ∫ b, F a b ∂(gaussianReal 0 1) = ∫ b, φ b * F a b := by
    intro a
    rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (f := fun b => F a b)
      (by norm_num : (1:NNReal) ≠ 0)]
    exact integral_congr_ae (ae_of_all _ fun b => by simp [hφ, smul_eq_mul])
  have hQ1 : ∫ a, (∫ b, F a b ∂(gaussianReal 0 1)) ∂(gaussianReal 0 1)
      = ∫ a, φ a * (∫ b, φ b * F a b) := by
    rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1)
      (f := fun a => ∫ b, F a b ∂(gaussianReal 0 1)) (by norm_num : (1:NNReal) ≠ 0)]
    exact integral_congr_ae (ae_of_all _ fun a => by simp only [hγ1 a, hφ, smul_eq_mul])
  rw [hQ1]
  -- inner substitution `b ↦ (y - t a)/s`
  have hsub : ∀ a : ℝ, ∫ b, φ b * F a b
      = s⁻¹ * ∫ y, (if a * y < 0 then (1:ℝ) else 0) * φ ((y - t * a) / s) := by
    intro a
    have hsk := GW.inner_skew_subst t s a hs (fun y => if a * y < 0 then (1:ℝ) else 0)
    rw [← hsk]
    exact integral_congr_ae (ae_of_all _ fun b => by simp only [hφ, hF, mul_comm])
  -- identify with `R`
  have hR : ∀ a : ℝ, φ a * (s⁻¹ * ∫ y, (if a * y < 0 then (1:ℝ) else 0) * φ ((y - t * a) / s))
      = ∫ y, (if a * y < 0 then (1:ℝ) else 0) * GW.R t s a y := by
    intro a
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    have hskew := GW.gauss_prod_skew (t := t) (s := s) hs a y
    simp only [hφ, GW.R]
    calc gaussianPDFReal 0 1 a * (s⁻¹ * ((if a * y < 0 then (1:ℝ) else 0) * gaussianPDFReal 0 1 ((y - t * a) / s)))
        = (if a * y < 0 then (1:ℝ) else 0) * (s⁻¹ * (gaussianPDFReal 0 1 a * gaussianPDFReal 0 1 ((y - t * a) / s))) := by ring
      _ = (if a * y < 0 then (1:ℝ) else 0) * (s⁻¹ * (s * (gaussianPDFReal 0 1 a * gaussianPDFReal (t * a) (GW.ssq s) y))) := by rw [hskew]
      _ = (if a * y < 0 then (1:ℝ) else 0) * (gaussianPDFReal 0 1 a * gaussianPDFReal (t * a) (GW.ssq s) y) := by
            field_simp
  simp only [hsub, hR]
  -- split the sign regions and evaluate
  have hinnerEq : ∀ a : ℝ, ∫ y, (if a * y < 0 then (1:ℝ) else 0) * GW.R t s a y
      = (if 0 < a then ∫ y in Iio 0, GW.R t s a y else 0)
        + (if a < 0 then ∫ y in Ioi 0, GW.R t s a y else 0) := by
    intro a
    have hfun : (fun y => (if a * y < 0 then (1:ℝ) else 0) * GW.R t s a y)
        = fun y => (if 0 < a ∧ y < 0 then (1:ℝ) else 0) * GW.R t s a y
            + (if a < 0 ∧ 0 < y then (1:ℝ) else 0) * GW.R t s a y := by
      funext y; rw [split_indicator]; ring
    have hI1 : Integrable (fun y => (if 0 < a ∧ y < 0 then (1:ℝ) else 0) * GW.R t s a y) := by
      by_cases ha : 0 < a
      · have : (fun y => (if 0 < a ∧ y < 0 then (1:ℝ) else 0) * GW.R t s a y)
            = Set.indicator (Iio 0) (fun y => GW.R t s a y) := by
          funext y; by_cases hy : y < 0 <;> simp [ha, hy]
        rw [this]
        exact (GW.integrable_R_slice (t := t) (s := s) a).indicator measurableSet_Iio
      · have : (fun y => (if 0 < a ∧ y < 0 then (1:ℝ) else 0) * GW.R t s a y) = fun _ => 0 := by
          funext y; simp [ha]
        rw [this]; exact integrable_zero _ _ _
    have hI2 : Integrable (fun y => (if a < 0 ∧ 0 < y then (1:ℝ) else 0) * GW.R t s a y) := by
      by_cases ha : a < 0
      · have : (fun y => (if a < 0 ∧ 0 < y then (1:ℝ) else 0) * GW.R t s a y)
            = Set.indicator (Ioi 0) (fun y => GW.R t s a y) := by
          funext y; by_cases hy : 0 < y <;> simp [ha, hy]
        rw [this]
        exact (GW.integrable_R_slice (t := t) (s := s) a).indicator measurableSet_Ioi
      · have : (fun y => (if a < 0 ∧ 0 < y then (1:ℝ) else 0) * GW.R t s a y) = fun _ => 0 := by
          funext y; simp [ha]
        rw [this]; exact integrable_zero _ _ _
    rw [hfun, integral_add hI1 hI2]
    congr 1
    · by_cases ha : 0 < a
      · rw [if_pos ha]
        have : (fun y => (if 0 < a ∧ y < 0 then (1:ℝ) else 0) * GW.R t s a y)
            = Set.indicator (Iio 0) (fun y => GW.R t s a y) := by
          funext y; by_cases hy : y < 0 <;> simp [ha, hy]
        rw [this, integral_indicator measurableSet_Iio]
      · rw [if_neg ha]
        have : (fun y => (if 0 < a ∧ y < 0 then (1:ℝ) else 0) * GW.R t s a y) = fun _ => 0 := by
          funext y; simp [ha]
        rw [this]; simp
    · by_cases ha : a < 0
      · rw [if_pos ha]
        have : (fun y => (if a < 0 ∧ 0 < y then (1:ℝ) else 0) * GW.R t s a y)
            = Set.indicator (Ioi 0) (fun y => GW.R t s a y) := by
          funext y; by_cases hy : 0 < y <;> simp [ha, hy]
        rw [this, integral_indicator measurableSet_Ioi]
      · rw [if_neg ha]
        have : (fun y => (if a < 0 ∧ 0 < y then (1:ℝ) else 0) * GW.R t s a y) = fun _ => 0 := by
          funext y; simp [ha]
        rw [this]; simp
  simp only [hinnerEq]
  rw [integral_add (GW.integrable_outer_pos hs) (GW.integrable_outer_neg hs)]
  have hP : ∫ a, (if 0 < a then ∫ y in Iio 0, GW.R t s a y else 0)
      = ∫ a in Ioi 0, ∫ y in Iio 0, GW.R t s a y := by
    rw [show (fun a => if 0 < a then ∫ y in Iio 0, GW.R t s a y else 0)
        = Set.indicator (Ioi 0) (fun a => ∫ y in Iio 0, GW.R t s a y) from
      funext fun a => by by_cases ha : 0 < a <;> simp [ha]]
    rw [integral_indicator measurableSet_Ioi]
  have hN : ∫ a, (if a < 0 then ∫ y in Ioi 0, GW.R t s a y else 0)
      = ∫ a in Iio 0, ∫ y in Ioi 0, GW.R t s a y := by
    rw [show (fun a => if a < 0 then ∫ y in Ioi 0, GW.R t s a y else 0)
        = Set.indicator (Iio 0) (fun a => ∫ y in Ioi 0, GW.R t s a y) from
      funext fun a => by by_cases ha : a < 0 <;> simp [ha]]
    rw [integral_indicator measurableSet_Iio]
  rw [hP, hN]
  have hflip1 : ∫ a in Ioi 0, ∫ y in Iio 0, GW.R t s a y
      = ∫ a in Ioi 0, ∫ y in Ioi 0, GW.R (-t) s a y := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun a _ => ?_)
    rw [GW.setIntegral_neg_Iio (fun y => GW.R t s a y)]
    exact setIntegral_congr_fun measurableSet_Ioi (fun y _ => by rw [GW.R_flip_y])
  have hflip2 : ∫ a in Iio 0, ∫ y in Ioi 0, GW.R t s a y
      = ∫ a in Ioi 0, ∫ y in Ioi 0, GW.R (-t) s a y := by
    rw [GW.setIntegral_neg_Iio (fun a => ∫ y in Ioi 0, GW.R t s a y)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun a _ => ?_)
    exact setIntegral_congr_fun measurableSet_Ioi (fun y _ => by rw [GW.R_flip_x])
  rw [hflip1, hflip2]
  have hquad : ∫ a in Ioi 0, ∫ y in Ioi 0, GW.R (-t) s a y
      = 1 / 4 + Real.arcsin (-t) / (2 * Real.pi) := by
    refine GW.integral_R_quadrant (t := t) (s := s) (e := -t) hs ?_ ?_ ?_ ?_
    · simpa using hs2
    · ring
    · linarith
    · linarith
  rw [hquad, Real.arcsin_neg]
  have hfin : 1 / 4 + -Real.arcsin t / (2 * Real.pi)
      + (1 / 4 + -Real.arcsin t / (2 * Real.pi)) = Real.arccos t / Real.pi := by
    rw [Real.arccos_eq_pi_div_two_sub_arcsin]
    field_simp
    ring
  rw [hfin]

end GWc



namespace QuantumMaxCutEnergy

/-- **Goemans–Williamson hyperplane rounding.** For unit vectors `v i` in `ℝ^D` with `D ≥ 1`,
the expected cut value of the random hyperplane rounding `sign ⟨g, v i⟩` (with `g` standard
Gaussian) equals `∑ e, w e * arccos ⟨v i, v j⟩ / π`. -/
theorem gw_rounding_expectation (G : Input) (D : ℕ) (hD : 1 ≤ D)
    (v : Fin G.n → EuclideanSpace ℝ (Fin D))
    (hunit : ∀ i, ‖v i‖ = 1) :
    ∫ g : EuclideanSpace ℝ (Fin D),
        (∑ e : Edge G.n, (G.weights e : ℝ) *
          (if Real.sign (inner ℝ (v e.val.1) g) = Real.sign (inner ℝ (v e.val.2) g) then 0 else 1))
      ∂(stdGaussian (EuclideanSpace ℝ (Fin D))) =
    ∑ e : Edge G.n, (G.weights e : ℝ) * Real.arccos (inner ℝ (v e.val.1) (v e.val.2)) / Real.pi :=
  gw_rounding_expectation_of_nondeg D
    (fun u w hu hw h1 h2 => GWc.nondeg_quad u w hu hw h1 h2) G v hunit

end QuantumMaxCutEnergy

/-- Goemans–Williamson rounding, packaged as the platform solution. -/
theorem solution (G : QuantumMaxCutEnergy.Input) (D : ℕ) (hD : 1 ≤ D)
    (v : Fin G.n → EuclideanSpace ℝ (Fin D))
    (hunit : ∀ i, ‖v i‖ = 1) :
    ∫ g : EuclideanSpace ℝ (Fin D),
        (∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) *
          (if Real.sign (inner ℝ (v e.val.1) g) = Real.sign (inner ℝ (v e.val.2) g) then 0 else 1))
      ∂(stdGaussian (EuclideanSpace ℝ (Fin D))) =
    ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) * Real.arccos (inner ℝ (v e.val.1) (v e.val.2)) / Real.pi :=
  QuantumMaxCutEnergy.gw_rounding_expectation G D hD v hunit

#print axioms solution
