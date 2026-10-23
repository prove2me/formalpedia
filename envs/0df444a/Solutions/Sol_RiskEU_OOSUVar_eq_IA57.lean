-- Prove2me | solution 1 for RiskEU.OOSUVar.eq_IA57
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T11:28:19.670382+00:00
-- url     : https://prove2.me/submissions/8a2013e3-fdc2-4dba-8e11-c99b81d99ad8

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting
import Definitions.Def_RiskEU_OOSUVar_KanRepresentation

open MeasureTheory ProbabilityTheory Real Set Filter Topology


open RiskEU.OOSUVar

namespace ChiTest

/-- Laplace transform of `x²` under the standard normal. -/
lemma gauss_laplace_sq {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, rexp (-t * x ^ 2) ∂(gaussianReal 0 1) = (1 + 2 * t) ^ (-(1 / 2 : ℝ)) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [gaussianPDFReal, smul_eq_mul, sub_zero, NNReal.coe_one, mul_one]
  have : (fun x : ℝ => (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) * rexp (-t * x ^ 2)) =
      fun x => (√(2 * π))⁻¹ * rexp (-(t + 1 / 2) * x ^ 2) := by
    funext x; rw [mul_assoc, ← Real.exp_add]; ring_nf
  rw [this, integral_const_mul, integral_gaussian]
  have h1 : 0 < 1 + 2 * t := by linarith
  rw [show π / (t + 1 / 2) = (2 * π) / (1 + 2 * t) by field_simp; ring,
    Real.sqrt_div' _ h1.le, Real.rpow_neg h1.le, ← Real.sqrt_eq_rpow]
  have : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  field_simp

lemma chiSq_laplace (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ q, rexp (-t * q) ∂(chiSq k) = (1 + 2 * t) ^ (-(k / 2 : ℝ)) := by
  unfold chiSq
  rw [integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  have : (fun g : Fin k → ℝ => rexp (-t * ∑ j, g j ^ 2)) =
      fun g => ∏ j, rexp (-t * g j ^ 2) := by
    funext g; rw [← Real.exp_sum, Finset.mul_sum]
  rw [this, integral_fintype_prod_eq_pow (fun x => rexp (-t * x ^ 2)), gauss_laplace_sq ht,
    Fintype.card_fin, ← Real.rpow_mul_natCast (by linarith)]
  congr 1; ring

end ChiTest



namespace ChiTest

lemma base_int {b : ℝ} (hb : 1 < b) :
    IntegrableOn (fun t : ℝ => (1 + 2 * t) ^ (-b)) (Ioi 0) ∧
    ∫ t in Ioi (0:ℝ), (1 + 2 * t) ^ (-b) = 1 / (2 * (b - 1)) := by
  set g : ℝ → ℝ := fun t => -(1 + 2 * t) ^ (1 - b) / (2 * (b - 1)) with hg
  have hb1 : b - 1 ≠ 0 := by linarith
  have hderiv : ∀ x ∈ Ici (0:ℝ), HasDerivAt g ((1 + 2 * x) ^ (-b)) x := by
    intro x hx
    have hx' : 0 < 1 + 2 * x := by simp at hx; linarith
    have h1 : HasDerivAt (fun t : ℝ => 1 + 2 * t) 2 x := by
      simpa using ((hasDerivAt_id x).const_mul 2).const_add 1
    have h2 := (h1.rpow_const (p := 1 - b) (Or.inl hx'.ne')).const_mul (-1 / (2 * (b - 1)))
    have e : g = fun y => (-1 / (2 * (b - 1))) * (1 + 2 * y) ^ (1 - b) := by
      funext y; simp only [hg]; ring
    rw [e]
    refine h2.congr_deriv ?_
    rw [show (1 - b - 1) = -b by ring]
    field_simp
    ring
  have hcont : ContinuousWithinAt g (Ici 0) 0 :=
    (hderiv 0 (by simp)).continuousAt.continuousWithinAt
  have hderiv' : ∀ x ∈ Ioi (0:ℝ), HasDerivAt g ((1 + 2 * x) ^ (-b)) x :=
    fun x hx => hderiv x (Ioi_subset_Ici_self hx)
  have hpos : ∀ x ∈ Ioi (0:ℝ), 0 ≤ (1 + 2 * x) ^ (-b) := fun x hx => by
    simp at hx; positivity
  have hlim : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => 1 + 2 * t) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop two_pos)
    have h2 := (tendsto_rpow_neg_atTop (y := b - 1) (by linarith)).comp h1
    have h3 := (h2.neg).div_const (2 * (b - 1))
    simp only [neg_zero, zero_div] at h3
    refine h3.congr fun t => ?_
    simp only [Function.comp_apply, hg]
    rw [show -(b - 1) = 1 - b by ring]
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hcont hderiv' hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv' hpos hlim]
  simp [hg]
  field_simp

/-- Closed form of `∫_0^∞ t^m (1+2t)^{-a} dt`. -/
noncomputable def Fm (m : ℕ) (a : ℝ) : ℝ :=
  (m.factorial : ℝ) / (2 ^ (m + 1) * ∏ i ∈ Finset.range (m + 1), (a - 1 - i))

lemma prod_pos_of {m : ℕ} {a : ℝ} (ha : (m : ℝ) + 1 < a) :
    0 < ∏ i ∈ Finset.range (m + 1), (a - 1 - i) := by
  apply Finset.prod_pos
  intro i hi
  have : (i : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  linarith

lemma Fm_succ (m : ℕ) (a : ℝ) (ha : (m : ℝ) + 2 < a) :
    Fm (m + 1) a = (Fm m (a - 1) - Fm m a) / 2 := by
  unfold Fm
  set P := ∏ i ∈ Finset.range (m + 1), (a - 1 - 1 - (i : ℝ)) with hP
  set R := ∏ i ∈ Finset.range (m + 1), (a - 1 - (i : ℝ)) with hR
  have h1 : ∏ i ∈ Finset.range (m + 1 + 1), (a - 1 - (i : ℝ)) = P * (a - 1) := by
    rw [Finset.prod_range_succ', hP]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      push_cast; ring
    · simp
  have h2 : ∏ i ∈ Finset.range (m + 1 + 1), (a - 1 - (i : ℝ)) = R * (a - 1 - (m + 1 : ℕ)) := by
    rw [Finset.prod_range_succ]
  have hPpos : 0 < P := by
    have := prod_pos_of (m := m) (a := a - 1) (by linarith)
    simpa [hP] using this
  have hRpos : 0 < R := prod_pos_of (m := m) (a := a) (by linarith)
  have key : P * (a - 1) = R * (a - m - 2) := by
    rw [← h1, h2]; push_cast; ring
  rw [h1, Nat.factorial_succ]
  have ha1 : a - 1 ≠ 0 := by intro h; linarith
  have ham : (a - m - 2) ≠ 0 := by intro h; linarith
  have hR' : R = P * (a - 1) / (a - m - 2) := by rw [key]; field_simp
  rw [hR']
  push_cast
  field_simp
  ring

lemma rec_int (m : ℕ) : ∀ a : ℝ, (m : ℝ) + 1 < a →
    IntegrableOn (fun t : ℝ => t ^ m * (1 + 2 * t) ^ (-a)) (Ioi 0) ∧
    ∫ t in Ioi (0:ℝ), t ^ m * (1 + 2 * t) ^ (-a) = Fm m a := by
  induction m with
  | zero =>
    intro a ha
    simp only [Nat.cast_zero, zero_add] at ha
    obtain ⟨h1, h2⟩ := base_int ha
    simp only [pow_zero, one_mul]
    refine ⟨h1, ?_⟩
    rw [h2, Fm]
    simp
  | succ m ih =>
    intro a ha
    push_cast at ha
    obtain ⟨i1, e1⟩ := ih (a - 1) (by linarith)
    obtain ⟨i2, e2⟩ := ih a (by linarith)
    have hpt : ∀ t ∈ Ioi (0:ℝ), t ^ (m + 1) * (1 + 2 * t) ^ (-a) =
        (t ^ m * (1 + 2 * t) ^ (-(a - 1)) - t ^ m * (1 + 2 * t) ^ (-a)) / 2 := by
      intro t ht
      have hp : 0 < 1 + 2 * t := by simp at ht; linarith
      rw [show -(a - 1) = 1 + -a by ring, Real.rpow_add hp, Real.rpow_one]
      ring
    have hint : IntegrableOn (fun t : ℝ => t ^ (m + 1) * (1 + 2 * t) ^ (-a)) (Ioi 0) := by
      have hi : IntegrableOn (fun t : ℝ => (t ^ m * (1 + 2 * t) ^ (-(a - 1)) -
          t ^ m * (1 + 2 * t) ^ (-a)) / 2) (Ioi (0:ℝ)) := (i1.sub i2).div_const 2
      exact hi.congr_fun (fun t ht => (hpt t ht).symm) measurableSet_Ioi
    refine ⟨hint, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_div, integral_sub i1 i2, e1, e2,
      Fm_succ m a (by linarith)]

end ChiTest



namespace ChiTest

lemma gauss_int_pow (n : ℕ) : Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) (n : NNReal)).integrable_norm_pow (by positivity)
  refine h.mono' ?_ ?_
  · exact (by fun_prop : Measurable fun x : ℝ => x ^ n).aestronglyMeasurable
  · exact ae_of_all _ fun x => by simp [norm_pow]

lemma gauss_moment (n : ℕ) :
    ∫ x, x ^ n ∂(gaussianReal 0 1) = iteratedDeriv n (fun t : ℝ => rexp (t ^ 2 / 2)) 0 := by
  have := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 1) (by simp) n
  rw [mgf_fun_id_gaussianReal] at this
  simp only [zero_mul, zero_add, NNReal.coe_one, one_mul] at this
  rw [this]; rfl

lemma gauss_moment2 : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  rw [gauss_moment]
  have d1 : deriv (fun t : ℝ => rexp (t ^ 2 / 2)) = fun t => t * rexp (t ^ 2 / 2) := by
    ext t; rw [_root_.deriv_exp (by fun_prop)]; simp; ring
  rw [iteratedDeriv_succ, iteratedDeriv_one, d1, deriv_fun_mul (by fun_prop) (by fun_prop)]
  simp

lemma gauss_moment4 : ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  rw [gauss_moment]
  have d1 : deriv (fun t : ℝ => rexp (t ^ 2 / 2)) = fun t => t * rexp (t ^ 2 / 2) := by
    ext t; rw [_root_.deriv_exp (by fun_prop)]; simp; ring
  have d2 : deriv (fun t : ℝ => t * rexp (t ^ 2 / 2)) = fun t => (1 + t ^ 2) * rexp (t ^ 2 / 2) := by
    ext t; rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    rw [show deriv (fun t : ℝ => rexp (t ^ 2 / 2)) t = t * rexp (t ^ 2 / 2) by rw [d1]]
    simp; ring
  have d3 : deriv (fun t : ℝ => (1 + t ^ 2) * rexp (t ^ 2 / 2)) =
      fun t => (3 * t + t ^ 3) * rexp (t ^ 2 / 2) := by
    ext t; rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    rw [show deriv (fun t : ℝ => rexp (t ^ 2 / 2)) t = t * rexp (t ^ 2 / 2) by rw [d1]]
    simp; ring
  have d4 : deriv (fun t : ℝ => (3 * t + t ^ 3) * rexp (t ^ 2 / 2)) =
      fun t => (3 + 6 * t ^ 2 + t ^ 4) * rexp (t ^ 2 / 2) := by
    ext t; rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    rw [show deriv (fun t : ℝ => rexp (t ^ 2 / 2)) t = t * rexp (t ^ 2 / 2) by rw [d1]]
    have h3 : deriv (fun t : ℝ => 3 * t + t ^ 3) t = 3 + 3 * t ^ 2 := by
      have : HasDerivAt (fun t : ℝ => 3 * t + t ^ 3) (3 * 1 + (3 : ℕ) * t ^ 2) t :=
        ((hasDerivAt_id t).const_mul 3).fun_add (hasDerivAt_pow 3 t)
      rw [this.deriv]; push_cast; ring
    rw [h3]; ring
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, d1, d2, d3, d4]
  norm_num

end ChiTest

namespace ChiTest


lemma pi_eval_integral {k : ℕ} (j : Fin k) (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ g, f (g j) ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1) = ∫ x, f x ∂(gaussianReal 0 1) := by
  rw [← integral_map (measurable_pi_apply j).aemeasurable hf.aestronglyMeasurable,
    (measurePreserving_eval (fun _ : Fin k => gaussianReal 0 1) j).map_eq]

lemma pi_eval_integrable {k : ℕ} (j : Fin k) (f : ℝ → ℝ) (hf : Measurable f)
    (h : Integrable f (gaussianReal 0 1)) : Integrable (fun g => f (g j)) (Measure.pi fun _ : Fin k => gaussianReal 0 1) := by
  have := (measurePreserving_eval (fun _ : Fin k => gaussianReal 0 1) j)
  rw [← this.map_eq] at h
  exact (integrable_map_measure hf.aestronglyMeasurable (measurable_pi_apply j).aemeasurable).1 h

lemma pi_indep {k : ℕ} : iIndepFun (fun (i : Fin k) (g : Fin k → ℝ) => g i) (Measure.pi fun _ : Fin k => gaussianReal 0 1) :=
  iIndepFun_pi (X := fun _ (x : ℝ) => x) (fun _ => aemeasurable_id)

lemma pi_sq_mul {k : ℕ} (i j : Fin k) :
    ∫ g, g i ^ 2 * g j ^ 2 ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1) = if i = j then 3 else 1 := by
  split_ifs with h
  · subst h
    simp_rw [← pow_add]
    rw [pi_eval_integral i (fun x => x ^ (2 + 2)) (by fun_prop)]
    exact gauss_moment4
  · have hind := (pi_indep.indepFun h).comp (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2)
      (by fun_prop) (by fun_prop)
    have := hind.integral_fun_mul_eq_mul_integral
      ((measurable_pi_apply i).pow_const 2).aestronglyMeasurable
      ((measurable_pi_apply j).pow_const 2).aestronglyMeasurable
    simp only [Function.comp_def] at this
    rw [this, pi_eval_integral i (fun x => x ^ 2) (by fun_prop),
      pi_eval_integral j (fun x => x ^ 2) (by fun_prop), gauss_moment2]
    norm_num

lemma chiSq_meas (k : ℕ) : Measurable (fun g : Fin k → ℝ => ∑ j, g j ^ 2) := by fun_prop

open RiskEU.OOSUVar in
lemma chiSq_map_integral (k : ℕ) (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ q, f q ∂(chiSq k) = ∫ g, f (∑ j, g j ^ 2) ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1) := by
  unfold chiSq
  rw [integral_map (chiSq_meas k).aemeasurable hf.aestronglyMeasurable]

open RiskEU.OOSUVar in
lemma chiSq_map_integrable (k : ℕ) (f : ℝ → ℝ) (hf : Measurable f) :
    Integrable f (chiSq k) ↔ Integrable (fun g => f (∑ j, g j ^ 2)) (Measure.pi fun _ : Fin k => gaussianReal 0 1) := by
  unfold chiSq
  exact integrable_map_measure hf.aestronglyMeasurable (chiSq_meas k).aemeasurable

lemma pi_sq_integrable {k : ℕ} (i : Fin k) : Integrable (fun g : Fin k → ℝ => g i ^ 2) (Measure.pi fun _ : Fin k => gaussianReal 0 1) :=
  pi_eval_integrable i (fun x => x ^ 2) (by fun_prop) (gauss_int_pow 2)

lemma pi_sq_mul_integrable {k : ℕ} (i j : Fin k) :
    Integrable (fun g : Fin k → ℝ => g i ^ 2 * g j ^ 2) (Measure.pi fun _ : Fin k => gaussianReal 0 1) := by
  have h4 : ∀ l : Fin k, Integrable (fun g : Fin k → ℝ => g l ^ 4) (Measure.pi fun _ : Fin k => gaussianReal 0 1) := fun l =>
    pi_eval_integrable l (fun x => x ^ 4) (by fun_prop) (gauss_int_pow 4)
  refine ((h4 i).add (h4 j)).mono' (by fun_prop) (ae_of_all _ fun g => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (g i ^ 2 - g j ^ 2)]

open RiskEU.OOSUVar in
lemma chiSq_moment1 (k : ℕ) :
    Integrable (fun q : ℝ => q) (chiSq k) ∧ ∫ q, q ∂(chiSq k) = k := by
  rw [chiSq_map_integrable k (fun q => q) measurable_id', chiSq_map_integral k (fun q => q) measurable_id']
  refine ⟨integrable_finsetSum _ fun i _ => pi_sq_integrable i, ?_⟩
  rw [integral_finsetSum _ fun i _ => pi_sq_integrable i]
  simp_rw [fun i => pi_eval_integral i (fun x => x ^ 2) (by fun_prop), gauss_moment2]
  simp

open RiskEU.OOSUVar in
lemma chiSq_moment2 (k : ℕ) :
    Integrable (fun q : ℝ => q ^ 2) (chiSq k) ∧ ∫ q, q ^ 2 ∂(chiSq k) = k * (k + 2) := by
  rw [chiSq_map_integrable k _ (by fun_prop), chiSq_map_integral k _ (by fun_prop)]
  have hexp : (fun g : Fin k → ℝ => (∑ j, g j ^ 2) ^ 2) =
      fun g => ∑ i, ∑ j, g i ^ 2 * g j ^ 2 := by
    funext g; rw [sq, Finset.sum_mul_sum]
  rw [hexp]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    pi_sq_mul_integrable i j, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => pi_sq_mul_integrable i j]
  simp_rw [integral_finsetSum _ fun j _ => pi_sq_mul_integrable _ j, pi_sq_mul]
  rw [Finset.sum_congr rfl fun i _ => (show (∑ j : Fin k, if i = j then (3:ℝ) else 1) = k + 2 by
    have : ∀ j, (if i = j then (3:ℝ) else 1) = 1 + if i = j then 2 else 0 := by
      intro j; split_ifs <;> norm_num
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq]; simp)]
  simp; ring

end ChiTest

namespace ChiTest
open RiskEU.OOSUVar

instance chiSq_prob (k : ℕ) : IsProbabilityMeasure (chiSq k) := by
  unfold chiSq
  exact Measure.isProbabilityMeasure_map (chiSq_meas k).aemeasurable

lemma chiSq_ae_pos {k : ℕ} (hk : 1 ≤ k) : ∀ᵐ q ∂(chiSq k), 0 < q := by
  unfold chiSq
  rw [ae_map_iff (chiSq_meas k).aemeasurable (measurableSet_lt measurable_const measurable_id')]
  set j : Fin k := ⟨0, hk⟩
  have h0 : (Measure.pi fun _ : Fin k => gaussianReal 0 1) {g | g j = 0} = 0 := by
    have hpre := (measurePreserving_eval (fun _ : Fin k => gaussianReal 0 1) j).measure_preimage
      (s := {0}) (measurableSet_singleton 0).nullMeasurableSet
    have : (fun g : Fin k → ℝ => g j) ⁻¹' {0} = {g | g j = 0} := rfl
    rw [this] at hpre
    rw [hpre]
    exact gaussianReal_absolutelyContinuous 0 (by norm_num) (Real.volume_singleton)
  have : ∀ᵐ g ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1), g j ≠ 0 := by
    rw [ae_iff]; simpa using h0
  filter_upwards [this] with g hg
  calc (0:ℝ) < g j ^ 2 := by positivity
    _ ≤ ∑ i, g i ^ 2 := Finset.single_le_sum (f := fun i => g i ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j)

lemma inv_pow_eq_integral (n : ℕ) {q : ℝ} (hq : 0 < q) :
    (q ^ (n + 1))⁻¹ = ∫ t in Ioi (0:ℝ), t ^ n * rexp (-(q * t)) / n.factorial := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := q) (by positivity) hq
  rw [show ((n:ℝ) + 1 - 1) = (n : ℝ) by ring] at h
  have h2 : ∫ t in Ioi (0:ℝ), t ^ n * rexp (-(q * t)) =
      ∫ t in Ioi (0:ℝ), t ^ (n : ℝ) * rexp (-(q * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp [Real.rpow_natCast]
  rw [integral_div, h2, h, Real.Gamma_nat_eq_factorial,
    show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  simp [one_div, inv_pow]
  exact (mul_inv_cancel₀ (by positivity)).symm

end ChiTest

namespace ChiTest
open RiskEU.OOSUVar

lemma chiSq_exp_integrable (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun q => rexp (-t * q)) (chiSq k) := by
  rw [chiSq_map_integrable k _ (by fun_prop)]
  refine (integrable_const (1:ℝ)).mono' (Measurable.aestronglyMeasurable (by fun_prop))
    (ae_of_all _ fun g => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  have : 0 ≤ ∑ j, g j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  nlinarith

lemma chiSq_inv_lintegral (k n : ℕ) (hk : 2 * n + 2 < k) :
    ∫⁻ q, ENNReal.ofReal ((q ^ (n + 1))⁻¹) ∂(chiSq k) =
      ENNReal.ofReal (Fm n ((k : ℝ) / 2) / n.factorial) := by
  have hk1 : 1 ≤ k := by omega
  have step1 : ∀ᵐ q ∂(chiSq k), ENNReal.ofReal ((q ^ (n + 1))⁻¹) =
      ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ n * rexp (-(q * t)) / n.factorial) := by
    filter_upwards [chiSq_ae_pos hk1] with q hq
    rw [inv_pow_eq_integral n hq]
    have hne : ∫ t in Ioi (0:ℝ), t ^ n * rexp (-(q * t)) / n.factorial ≠ 0 := by
      rw [← inv_pow_eq_integral n hq]; positivity
    refine ofReal_integral_eq_lintegral_ofReal (Integrable.of_integral_ne_zero hne) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht => ?_)
    simp only [Pi.zero_apply]
    have : 0 < t := ht
    positivity
  rw [lintegral_congr_ae step1]
  rw [lintegral_lintegral_swap (by
    apply Measurable.aemeasurable
    apply ENNReal.measurable_ofReal.comp
    fun_prop)]
  have step3 : ∀ t ∈ Ioi (0:ℝ), ∫⁻ q, ENNReal.ofReal (t ^ n * rexp (-(q * t)) / n.factorial)
      ∂(chiSq k) = ENNReal.ofReal (t ^ n * (1 + 2 * t) ^ (-((k : ℝ) / 2)) / n.factorial) := by
    intro t ht
    have ht' : 0 ≤ t := le_of_lt ht
    have e : ∀ q, ENNReal.ofReal (t ^ n * rexp (-(q * t)) / n.factorial) =
        ENNReal.ofReal (t ^ n / n.factorial) * ENNReal.ofReal (rexp (-t * q)) := by
      intro q
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1; ring_nf
    simp_rw [e]
    rw [lintegral_const_mul _ (by fun_prop),
      ← ofReal_integral_eq_lintegral_ofReal (chiSq_exp_integrable k ht')
        (ae_of_all _ fun q => (Real.exp_pos _).le),
      chiSq_laplace k ht', ← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring
  rw [setLIntegral_congr_fun measurableSet_Ioi step3]
  have ha : (n : ℝ) + 1 < (k : ℝ) / 2 := by
    have : ((2 * n + 2 : ℕ) : ℝ) < k := by exact_mod_cast hk
    push_cast at this; linarith
  obtain ⟨hi, he⟩ := rec_int n ((k : ℝ) / 2) ha
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.div_const _), integral_div, he]
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht => ?_)
  have : 0 < t := ht
  simp only [Pi.zero_apply]
  positivity

lemma Fm_half (n k : ℕ) :
    Fm n ((k : ℝ) / 2) / n.factorial =
      1 / ∏ i ∈ Finset.range (n + 1), ((k : ℝ) - 2 - 2 * i) := by
  unfold Fm
  have : ∏ i ∈ Finset.range (n + 1), ((k : ℝ) - 2 - 2 * i) =
      2 ^ (n + 1) * ∏ i ∈ Finset.range (n + 1), ((k : ℝ) / 2 - 1 - i) := by
    rw [show (2:ℝ) ^ (n + 1) = ∏ i ∈ Finset.range (n + 1), (2:ℝ) by simp,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => by ring
  rw [this]
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- Inverse moments of the chi-squared law: `E[Q^{-(n+1)}] = 1/∏_{i=0}^{n} (k-2-2i)`. -/
lemma chiSq_inv_moment (k n : ℕ) (hk : 2 * n + 2 < k) :
    Integrable (fun q : ℝ => (q ^ (n + 1))⁻¹) (chiSq k) ∧
    ∫ q, (q ^ (n + 1))⁻¹ ∂(chiSq k) = 1 / ∏ i ∈ Finset.range (n + 1), ((k : ℝ) - 2 - 2 * i) := by
  have hk1 : 1 ≤ k := by omega
  have hnn : 0 ≤ᵐ[chiSq k] fun q : ℝ => (q ^ (n + 1))⁻¹ := by
    filter_upwards [chiSq_ae_pos hk1] with q hq
    simp only [Pi.zero_apply]; positivity
  have hm : AEStronglyMeasurable (fun q : ℝ => (q ^ (n + 1))⁻¹) (chiSq k) := by fun_prop
  have hl := chiSq_inv_lintegral k n hk
  refine ⟨⟨hm, (hasFiniteIntegral_iff_ofReal hnn).2 (by rw [hl]; exact ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hm, hl, ENNReal.toReal_ofReal, Fm_half]
  rw [Fm_half]
  apply div_nonneg zero_le_one
  apply Finset.prod_nonneg
  intro i hi
  have : (i : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have : ((2 * n + 2 : ℕ) : ℝ) < k := by exact_mod_cast hk
  push_cast at this
  linarith

end ChiTest

namespace ChiTest
open RiskEU.OOSUVar

variable {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}

lemma law_integrable {Y : Ω' → ℝ} {μ : Measure ℝ} (h : HasLaw Y μ Q) {f : ℝ → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) : Integrable (fun ω => f (Y ω)) Q := by
  rw [← h.map_eq] at hi
  exact (integrable_map_measure hf.aestronglyMeasurable h.aemeasurable).1 hi

lemma law_integral {Y : Ω' → ℝ} {μ : Measure ℝ} (h : HasLaw Y μ Q) {f : ℝ → ℝ}
    (hf : Measurable f) : ∫ ω, f (Y ω) ∂Q = ∫ x, f x ∂μ :=
  h.integral_comp (f := f) hf.aestronglyMeasurable

lemma indep_one_three {X : KanVar → Ω' → ℝ} (hind : iIndepFun X Q)
    (hm : ∀ i, AEMeasurable (X i) Q) (i0 i1 i2 i3 : KanVar)
    (hab : i0 ≠ i1) (hac : i0 ≠ i2) (had : i0 ≠ i3) :
    IndepFun (X i0) (fun ω => (X i1 ω, X i2 ω, X i3 ω)) Q := by
  have hdis : Disjoint ({i0} : Finset KanVar) {i1, i2, i3} := by
    simp [hab, hac, had]
  have h := hind.indepFun_finset₀ {i0} {i1, i2, i3} hdis hm
  exact h.comp (φ := fun p : ({i0} : Finset KanVar) → ℝ => p ⟨i0, by simp⟩)
    (ψ := fun p : ({i1, i2, i3} : Finset KanVar) → ℝ =>
      (p ⟨i1, by simp⟩, p ⟨i2, by simp⟩, p ⟨i3, by simp⟩))
    (measurable_pi_apply (⟨i0, by simp⟩ : ({i0} : Finset KanVar)))
    ((measurable_pi_apply _).prodMk ((measurable_pi_apply _).prodMk (measurable_pi_apply _)))

end ChiTest

open RiskEU.OOSUVar ChiTest in
theorem solution {N T : ℕ} (hN : 2 ≤ N) (hT : N + 7 < T) (psi2 : ℝ) (hpsi2 : 0 ≤ psi2)
    {Ω' : Type*} [MeasurableSpace Ω'] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (X : KanVar → Ω' → ℝ) (hX : IsKanFamily N T psi2 Q X) :
    Integrable (fun ω' => 1 / X .v2 ω' ^ 4 *
        (1 + (KanVar.x21' N (fun i => X i ω') ^ 2 + X .s2 ω') / X .w2 ω') ^ 2) Q ∧
    ∫ ω', 1 / X .v2 ω' ^ 4 *
        (1 + (KanVar.x21' N (fun i => X i ω') ^ 2 + X .s2 ω') / X .w2 ω') ^ 2 ∂Q =
      ((T : ℝ) - 2) * ((T : ℝ) - 4) /
        (((T : ℝ) - N) * ((T : ℝ) - N - 1) * ((T : ℝ) - N - 2) * ((T : ℝ) - N - 3) *
          ((T : ℝ) - N - 5) * ((T : ℝ) - N - 7)) := by
  obtain ⟨hind, hlaw⟩ := hX
  have hm : ∀ i, AEMeasurable (X i) Q := fun i => (hlaw i).aemeasurable
  have hV : HasLaw (X .v2) (chiSq (T - N + 1)) Q := hlaw .v2
  have hW : HasLaw (X .w2) (chiSq (T - N + 2)) Q := hlaw .w2
  have hS : HasLaw (X .s2) (chiSq (N - 3)) Q := hlaw .s2
  have hZ : HasLaw (X .x21) (gaussianReal 0 1) Q := hlaw .x21
  set e : ℝ := if 3 ≤ N then 1 else 0 with he
  have he2 : e * e = e := by rw [he]; split_ifs <;> norm_num
  have hx' : ∀ ω, KanVar.x21' N (fun i => X i ω) ^ 2 = e * X .x21 ω ^ 2 := by
    intro ω; simp only [KanVar.x21', he]; split_ifs <;> simp
  -- random variables
  set A : Ω' → ℝ := fun ω => (X .v2 ω ^ (3 + 1))⁻¹ with hA
  set q : Ω' → ℝ := fun ω => e * X .x21 ω ^ 2 + X .s2 ω with hq
  set W1 : Ω' → ℝ := fun ω => (X .w2 ω ^ (0 + 1))⁻¹ with hW1
  set W2 : Ω' → ℝ := fun ω => (X .w2 ω ^ (1 + 1))⁻¹ with hW2
  have hfun : (fun ω' => 1 / X .v2 ω' ^ 4 *
        (1 + (KanVar.x21' N (fun i => X i ω') ^ 2 + X .s2 ω') / X .w2 ω') ^ 2) =
      fun ω => A ω * (1 + 2 * (q ω * W1 ω) + q ω ^ 2 * W2 ω) := by
    funext ω
    rw [hx']
    simp only [hA, hq, hW1, hW2]
    ring
  rw [hfun]
  -- independence
  have iV := indep_one_three hind hm .v2 .x21 .s2 .w2 (by decide) (by decide) (by decide)
  have iQW : IndepFun (fun ω => (X .x21 ω, X .s2 ω)) (X .w2) Q :=
    hind.indepFun_prodMk₀ hm .x21 .s2 .w2 (by decide) (by decide)
  have iZS : IndepFun (X .x21) (X .s2) Q := hind.indepFun (by decide)
  -- laws and moments
  have hk1 : 2 * 3 + 2 < T - N + 1 := by omega
  have hk2 : 2 * 1 + 2 < T - N + 2 := by omega
  obtain ⟨iA, eA⟩ := chiSq_inv_moment (T - N + 1) 3 hk1
  obtain ⟨iW1, eW1⟩ := chiSq_inv_moment (T - N + 2) 0 (by omega)
  obtain ⟨iW2, eW2⟩ := chiSq_inv_moment (T - N + 2) 1 hk2
  obtain ⟨iS1, eS1⟩ := chiSq_moment1 (N - 3)
  obtain ⟨iS2, eS2⟩ := chiSq_moment2 (N - 3)
  have IA : Integrable A Q := law_integrable hV (by fun_prop) iA
  have EA : ∫ ω, A ω ∂Q = _ := (law_integral hV (f := fun q : ℝ => (q ^ (3 + 1))⁻¹) (by fun_prop)).trans eA
  have IW1 : Integrable W1 Q := law_integrable hW (by fun_prop) iW1
  have EW1 : ∫ ω, W1 ω ∂Q = _ := (law_integral hW (f := fun q : ℝ => (q ^ (0 + 1))⁻¹) (by fun_prop)).trans eW1
  have IW2 : Integrable W2 Q := law_integrable hW (by fun_prop) iW2
  have EW2 : ∫ ω, W2 ω ∂Q = _ := (law_integral hW (f := fun q : ℝ => (q ^ (1 + 1))⁻¹) (by fun_prop)).trans eW2
  have IS1 : Integrable (X .s2) Q := law_integrable hS (f := fun q => q) measurable_id' iS1
  have ES1 : ∫ ω, X .s2 ω ∂Q = _ := (law_integral hS (f := fun q : ℝ => q) measurable_id').trans eS1
  have IS2 : Integrable (fun ω => X .s2 ω ^ 2) Q := law_integrable hS (by fun_prop) iS2
  have ES2 : ∫ ω, X .s2 ω ^ 2 ∂Q = _ := (law_integral hS (f := fun q : ℝ => q ^ 2) (by fun_prop)).trans eS2
  have IZ2 : Integrable (fun ω => X .x21 ω ^ 2) Q := law_integrable hZ (by fun_prop) (gauss_int_pow 2)
  have EZ2 : ∫ ω, X .x21 ω ^ 2 ∂Q = 1 := (law_integral hZ (f := fun q : ℝ => q ^ 2) (by fun_prop)).trans gauss_moment2
  have IZ4 : Integrable (fun ω => X .x21 ω ^ 4) Q := law_integrable hZ (by fun_prop) (gauss_int_pow 4)
  have EZ4 : ∫ ω, X .x21 ω ^ 4 ∂Q = 3 := (law_integral hZ (f := fun q : ℝ => q ^ 4) (by fun_prop)).trans gauss_moment4
  -- q and q²
  have IZS : Integrable (fun ω => X .x21 ω ^ 2 * X .s2 ω) Q :=
    (iZS.comp (φ := fun x : ℝ => x ^ 2) (ψ := id) (by fun_prop) measurable_id).integrable_mul IZ2 IS1
  have EZS : ∫ ω, X .x21 ω ^ 2 * X .s2 ω ∂Q = 1 * ∫ ω, X .s2 ω ∂Q := by
    rw [← EZ2]
    exact (iZS.comp (φ := fun x : ℝ => x ^ 2) (ψ := id) (by fun_prop) measurable_id).integral_fun_mul_eq_mul_integral
      (by fun_prop) (by fun_prop)
  have Iq : Integrable q Q := (IZ2.const_mul e).add IS1
  have Eq : ∫ ω, q ω ∂Q = e * 1 + ∫ ω, X .s2 ω ∂Q := by
    rw [hq, integral_add (IZ2.const_mul e) IS1, integral_const_mul, EZ2]
  have hq2 : (fun ω => q ω ^ 2) = fun ω => e * X .x21 ω ^ 4 + 2 * e * (X .x21 ω ^ 2 * X .s2 ω) +
      X .s2 ω ^ 2 := by
    funext ω; simp only [hq]; linear_combination (X .x21 ω ^ 4) * he2
  have Iq2 : Integrable (fun ω => q ω ^ 2) Q := by
    rw [hq2]; exact ((IZ4.const_mul e).add (IZS.const_mul (2 * e))).add IS2
  have Eq2 : ∫ ω, q ω ^ 2 ∂Q = e * 3 + 2 * e * (1 * ∫ ω, X .s2 ω ∂Q) + ∫ ω, X .s2 ω ^ 2 ∂Q := by
    rw [hq2, integral_add (f := fun ω => e * X .x21 ω ^ 4 + 2 * e * (X .x21 ω ^ 2 * X .s2 ω))
      (g := fun ω => X .s2 ω ^ 2) ((IZ4.const_mul e).add (IZS.const_mul (2 * e))) IS2,
      integral_add (f := fun ω => e * X .x21 ω ^ 4) (g := fun ω => 2 * e * (X .x21 ω ^ 2 * X .s2 ω))
        (IZ4.const_mul e) (IZS.const_mul (2 * e)), integral_const_mul,
      integral_const_mul, EZ4, EZS]
  -- products with W
  have iqW1 : IndepFun q W1 Q :=
    iQW.comp (φ := fun p : ℝ × ℝ => e * p.1 ^ 2 + p.2) (ψ := fun w : ℝ => (w ^ (0 + 1))⁻¹)
      (by fun_prop) (by fun_prop)
  have iqW2 : IndepFun (fun ω => q ω ^ 2) W2 Q :=
    iQW.comp (φ := fun p : ℝ × ℝ => (e * p.1 ^ 2 + p.2) ^ 2) (ψ := fun w : ℝ => (w ^ (1 + 1))⁻¹)
      (by fun_prop) (by fun_prop)
  have I1 : Integrable (fun ω => q ω * W1 ω) Q := iqW1.integrable_mul Iq IW1
  have I2 : Integrable (fun ω => q ω ^ 2 * W2 ω) Q := iqW2.integrable_mul Iq2 IW2
  have E1 : ∫ ω, q ω * W1 ω ∂Q = (∫ ω, q ω ∂Q) * ∫ ω, W1 ω ∂Q :=
    iqW1.integral_fun_mul_eq_mul_integral Iq.aestronglyMeasurable IW1.aestronglyMeasurable
  have E2 : ∫ ω, q ω ^ 2 * W2 ω ∂Q = (∫ ω, q ω ^ 2 ∂Q) * ∫ ω, W2 ω ∂Q :=
    iqW2.integral_fun_mul_eq_mul_integral Iq2.aestronglyMeasurable IW2.aestronglyMeasurable
  have IB : Integrable (fun ω => 1 + 2 * (q ω * W1 ω) + q ω ^ 2 * W2 ω) Q :=
    ((integrable_const 1).add (I1.const_mul 2)).add I2
  have EB : ∫ ω, (1 + 2 * (q ω * W1 ω) + q ω ^ 2 * W2 ω) ∂Q =
      1 + 2 * ((∫ ω, q ω ∂Q) * ∫ ω, W1 ω ∂Q) + (∫ ω, q ω ^ 2 ∂Q) * ∫ ω, W2 ω ∂Q := by
    rw [integral_add (f := fun ω => 1 + 2 * (q ω * W1 ω)) (g := fun ω => q ω ^ 2 * W2 ω)
      ((integrable_const 1).add (I1.const_mul 2)) I2,
      integral_add (f := fun _ => (1:ℝ)) (g := fun ω => 2 * (q ω * W1 ω))
        (integrable_const 1) (I1.const_mul 2), integral_const_mul, E1, E2]
    simp
  have iAB : IndepFun A (fun ω => 1 + 2 * (q ω * W1 ω) + q ω ^ 2 * W2 ω) Q :=
    iV.comp (φ := fun v : ℝ => (v ^ (3 + 1))⁻¹)
      (ψ := fun p : ℝ × ℝ × ℝ => 1 + 2 * ((e * p.1 ^ 2 + p.2.1) * (p.2.2 ^ (0 + 1))⁻¹) +
        (e * p.1 ^ 2 + p.2.1) ^ 2 * (p.2.2 ^ (1 + 1))⁻¹)
      (by fun_prop) (by fun_prop)
  refine ⟨iAB.integrable_mul IA IB, ?_⟩
  rw [iAB.integral_fun_mul_eq_mul_integral IA.aestronglyMeasurable IB.aestronglyMeasurable,
    EA, EB, Eq, Eq2, EW1, EW2, ES1, ES2]
  -- final algebra
  have hNT : N ≤ T := by omega
  have c1 : ((T - N + 1 : ℕ) : ℝ) = (T : ℝ) - N + 1 := by push_cast [Nat.cast_sub hNT]; ring
  have c2 : ((T - N + 2 : ℕ) : ℝ) = (T : ℝ) - N + 2 := by push_cast [Nat.cast_sub hNT]; ring
  have hTN : (N : ℝ) + 7 < T := by exact_mod_cast hT
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, c1, c2]
  norm_num
  simp only [show (T:ℝ) - N + 1 - 2 = T - N - 1 by ring, show (T:ℝ) - N - 1 - 2 = T - N - 3 by ring,
    show (T:ℝ) - N - 1 - 4 = T - N - 5 by ring, show (T:ℝ) - N - 1 - 6 = T - N - 7 by ring,
    show (T:ℝ) - N + 2 - 2 = T - N by ring]
  have h0 : (T : ℝ) - N ≠ 0 := by intro h; linarith
  have h1 : (T : ℝ) - N - 1 ≠ 0 := by intro h; linarith
  have h2 : (T : ℝ) - N - 2 ≠ 0 := by intro h; linarith
  have h3 : (T : ℝ) - N - 3 ≠ 0 := by intro h; linarith
  have h5 : (T : ℝ) - N - 5 ≠ 0 := by intro h; linarith
  have h7 : (T : ℝ) - N - 7 ≠ 0 := by intro h; linarith
  by_cases h3N : 3 ≤ N
  · have c3 : ((N - 3 : ℕ) : ℝ) = (N : ℝ) - 3 := by push_cast [Nat.cast_sub h3N]; ring
    simp only [he, if_pos h3N, c3]
    push_cast
    field_simp
    ring
  · have hN2 : N = 2 := by omega
    subst hN2
    simp only [he, if_neg h3N, Nat.cast_ofNat, Nat.reduceSub, Nat.cast_zero] at h0 h1 h2 h3 h5 h7 ⊢
    field_simp
    ring
