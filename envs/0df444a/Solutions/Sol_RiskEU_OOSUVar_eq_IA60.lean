-- Prove2me | solution 1 for RiskEU.OOSUVar.eq_IA60
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T11:46:06.046981+00:00
-- url     : https://prove2.me/submissions/c3b58e3d-9baa-459a-b384-0bff64226ba9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting
import Definitions.Def_RiskEU_OOSUVar_KanRepresentation
import Theorems.Thm_RiskEU_OOSUVar_kan_representation

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


namespace KanAux
open RiskEU.OOSUVar ChiTest

instance : Fintype KanVar where
  elems := {.z2, .u0, .v2, .w1, .w2, .s1, .s2, .x11, .x21, .a, .b, .c}
  complete := by intro x; cases x <;> simp

lemma measurable_x11' (N : ℕ) : Measurable (fun v : KanVar → ℝ => KanVar.x11' N v) := by
  unfold KanVar.x11'; split_ifs <;> fun_prop
lemma measurable_x21' (N : ℕ) : Measurable (fun v : KanVar → ℝ => KanVar.x21' N v) := by
  unfold KanVar.x21'; split_ifs <;> fun_prop
lemma measurable_c' (N : ℕ) : Measurable (fun v : KanVar → ℝ => KanVar.c' N v) := by
  unfold KanVar.c'; split_ifs <;> fun_prop
lemma measurable_y1 (N : ℕ) : Measurable (fun v : KanVar → ℝ => KanVar.y1 N v) := by
  have := measurable_x11' N; have := measurable_x21' N
  unfold KanVar.y1; fun_prop
lemma measurable_y2 (N : ℕ) : Measurable (fun v : KanVar → ℝ => KanVar.y2 N v) := by
  have := measurable_c' N
  unfold KanVar.y2; fun_prop

lemma measurable_kanMeanRep {N : ℕ} (M : Market N) (T : ℕ) (κ : ℝ) :
    Measurable (fun v : KanVar → ℝ => M.kanMeanRep T κ v) := by
  have := measurable_y1 N; have := measurable_x21' N
  unfold Market.kanMeanRep; fun_prop

lemma measurable_kanVarRep {N : ℕ} (M : Market N) (T : ℕ) (κ : ℝ) :
    Measurable (fun v : KanVar → ℝ => M.kanVarRep T κ v) := by
  have := measurable_y1 N; have := measurable_y2 N; have := measurable_x21' N
  unfold Market.kanVarRep; fun_prop

instance kanLaw_prob (N T : ℕ) (psi2 : ℝ) (i : KanVar) : IsProbabilityMeasure (kanLaw N T psi2 i) := by
  cases i <;> simp only [kanLaw] <;> infer_instance

lemma canonical_isKan (N T : ℕ) (psi2 : ℝ) :
    IsKanFamily N T psi2 (Measure.pi (kanLaw N T psi2)) (fun i (v : KanVar → ℝ) => v i) :=
  ⟨iIndepFun_pi (X := fun _ (x : ℝ) => x) (fun _ => aemeasurable_id),
    fun i => (measurePreserving_eval (kanLaw N T psi2) i).hasLaw⟩

end KanAux

namespace KanAux
open RiskEU.OOSUVar ChiTest

lemma prod_univ (g : KanVar → ℝ) : ∏ i, g i = g .z2 * g .u0 * g .v2 * g .w1 * g .w2 * g .s1 *
    g .s2 * g .x11 * g .x21 * g .a * g .b * g .c := by
  simp [Finset.univ, Fintype.elems]
  ring

variable {N T : ℕ} {psi2 : ℝ}

lemma mono_integrable (g : KanVar → ℝ → ℝ) (h : ∀ i, Integrable (g i) (kanLaw N T psi2 i)) :
    Integrable (fun v : KanVar → ℝ => ∏ i, g i (v i)) (Measure.pi (kanLaw N T psi2)) :=
  Integrable.fintype_prod h

lemma mono_integral (g : KanVar → ℝ → ℝ) :
    ∫ v, ∏ i, g i (v i) ∂(Measure.pi (kanLaw N T psi2)) = ∏ i, ∫ x, g i x ∂(kanLaw N T psi2 i) :=
  integral_fintype_prod_eq_prod g

lemma coord_ae (i : KanVar) {p : ℝ → Prop} (h : ∀ᵐ x ∂(kanLaw N T psi2 i), p x) :
    ∀ᵐ v ∂(Measure.pi (kanLaw N T psi2)), p (v i) :=
  (measurePreserving_eval (kanLaw N T psi2) i).quasiMeasurePreserving.ae h

lemma chiSq_ae_nonneg (k : ℕ) : ∀ᵐ q ∂(chiSq k), 0 ≤ q := by
  unfold chiSq
  rw [ae_map_iff (chiSq_meas k).aemeasurable (measurableSet_le measurable_const measurable_id')]
  exact ae_of_all _ fun g => Finset.sum_nonneg fun j _ => sq_nonneg _

/-- Flipping the signs of a set of standard normal coordinates preserves the canonical measure. -/
lemma flip_preserving (S : Finset KanVar)
    (hS : ∀ i ∈ S, kanLaw N T psi2 i = gaussianReal 0 1) :
    MeasurePreserving (fun (v : KanVar → ℝ) i => if i ∈ S then -v i else v i)
      (Measure.pi (kanLaw N T psi2)) (Measure.pi (kanLaw N T psi2)) := by
  refine measurePreserving_pi (kanLaw N T psi2) (kanLaw N T psi2)
    (f := fun i x => if i ∈ S then -x else x) fun i => ?_
  by_cases hi : i ∈ S
  · simp only [hi, if_true]
    refine ⟨measurable_neg, ?_⟩
    rw [hS i hi, gaussianReal_map_neg, neg_zero]
  · simp only [hi, if_false]
    exact MeasurePreserving.id _

lemma odd_integral_zero (S : Finset KanVar)
    (hS : ∀ i ∈ S, kanLaw N T psi2 i = gaussianReal 0 1) (J : (KanVar → ℝ) → ℝ)
    (hJm : Measurable J)
    (hJ : ∀ v, J (fun i => if i ∈ S then -v i else v i) = - J v) :
    ∫ v, J v ∂(Measure.pi (kanLaw N T psi2)) = 0 := by
  have hp := flip_preserving S hS
  have h1 : ∫ v, J (fun i => if i ∈ S then -v i else v i) ∂(Measure.pi (kanLaw N T psi2)) =
      ∫ v, J v ∂(Measure.pi (kanLaw N T psi2)) := by
    rw [← integral_map hp.measurable.aemeasurable hJm.aestronglyMeasurable, hp.map_eq]
  simp_rw [hJ, integral_neg] at h1
  linarith

lemma inv_sqrt_le (w : ℝ) : ‖(√w)⁻¹‖ ≤ 1 + |w⁻¹| := by
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  rcases le_or_gt w 0 with hw | hw
  · rw [Real.sqrt_eq_zero'.2 hw, inv_zero]; positivity
  rcases le_or_gt 1 w with h1 | h1
  · have : 1 ≤ √w := Real.one_le_sqrt.2 h1
    have : (√w)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
    have : 0 ≤ |w⁻¹| := abs_nonneg _
    linarith
  · have hs : 0 < √w := Real.sqrt_pos.2 hw
    have : w ≤ √w := by
      have h2 : √w ≤ 1 := Real.sqrt_le_one.mpr h1.le
      nlinarith [Real.mul_self_sqrt hw.le]
    rw [abs_of_pos (inv_pos.2 hw)]
    have : (√w)⁻¹ ≤ w⁻¹ := inv_anti₀ hw this
    linarith

lemma sqrt_le_one_add_abs (u : ℝ) : ‖√u‖ ≤ 1 + |u| := by
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rcases le_or_gt u 0 with hu | hu
  · rw [Real.sqrt_eq_zero'.2 hu]; positivity
  rcases le_or_gt 1 u with h1 | h1
  · have : √u ≤ u := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    rw [abs_of_pos hu]; linarith
  · have : √u ≤ 1 := Real.sqrt_le_one.mpr h1.le
    have := abs_nonneg u; linarith

end KanAux

namespace KanAux
open RiskEU.OOSUVar Matrix

lemma psi2_nonneg {N : ℕ} (M : Market N) (hS : M.Sigma.PosDef) : 0 ≤ M.psi2 := by
  have hSi : (M.Sigma⁻¹).PosSemidef := hS.posSemidef.inv
  set S := M.Sigma⁻¹ with hSdef
  have hsym : ∀ x y : Fin N → ℝ, x ⬝ᵥ (S *ᵥ y) = y ⬝ᵥ (S *ᵥ x) := by
    intro x y
    have hH : Sᵀ = S := by
      have := hSi.isHermitian
      rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
      exact this
    rw [dotProduct_mulVec, ← hH, vecMul_transpose, dotProduct_comm, hH]
  have hq : ∀ x : Fin N → ℝ, 0 ≤ x ⬝ᵥ (S *ᵥ x) := by
    intro x; simpa using hSi.dotProduct_mulVec_nonneg x
  set e := ones N
  set a := e ⬝ᵥ (S *ᵥ e) with ha
  set b := M.mu ⬝ᵥ (S *ᵥ e) with hb
  have hsg : M.sigmaG2 = a⁻¹ := rfl
  have hmuG : M.muG = b * a⁻¹ := rfl
  unfold Market.psi2
  rw [hmuG, hsg]
  by_cases ha0 : a = 0
  · simp [ha0]; exact hq _
  · set t := b / a
    have key : (M.mu - t • e) ⬝ᵥ (S *ᵥ (M.mu - t • e)) =
        M.mu ⬝ᵥ (S *ᵥ M.mu) - b ^ 2 / a := by
      simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
        dotProduct_smul, smul_eq_mul]
      rw [hsym e M.mu]
      simp only [t, ← hb, ← ha]
      field_simp
      ring
    have := hq (M.mu - t • e)
    rw [key] at this
    have e2 : (b * a⁻¹) ^ 2 / a⁻¹ = b ^ 2 / a := by field_simp
    rw [e2]; exact this

end KanAux

namespace KanAux
open RiskEU.OOSUVar ChiTest

lemma int_abs_gauss (m : ℝ) : Integrable (fun x : ℝ => |x|) (gaussianReal m 1) :=
  ((memLp_id_gaussianReal (μ := m) (v := 1) 1).integrable le_rfl).abs

lemma int_id_gauss (m : ℝ) : Integrable (fun x : ℝ => x) (gaussianReal m 1) :=
  (memLp_id_gaussianReal (μ := m) (v := 1) 1).integrable le_rfl

lemma int_sq_gauss (m : ℝ) : Integrable (fun x : ℝ => x ^ 2) (gaussianReal m 1) := by
  have := (memLp_id_gaussianReal (μ := m) (v := 1) 2).integrable_norm_pow (p := 2) (by norm_num)
  refine this.congr (ae_of_all _ fun x => ?_)
  simp [sq_abs]

lemma int_inv_chi {k : ℕ} (hk : 2 < k) : Integrable (fun x : ℝ => x⁻¹) (chiSq k) := by
  have := (chiSq_inv_moment k 0 (by omega)).1
  simpa using this

lemma int_inv2_chi {k : ℕ} (hk : 4 < k) : Integrable (fun x : ℝ => (x ^ 2)⁻¹) (chiSq k) := by
  have := (chiSq_inv_moment k 1 (by omega)).1
  simpa using this

lemma int_one_add_abs_inv_chi {k : ℕ} (hk : 2 < k) :
    Integrable (fun x : ℝ => 1 + |x⁻¹|) (chiSq k) :=
  (integrable_const 1).add (int_inv_chi hk).abs

lemma int_one_add_abs_chi (k : ℕ) : Integrable (fun x : ℝ => 1 + |x|) (chiSq k) :=
  (integrable_const 1).add (chiSq_moment1 k).1.abs

lemma abs_x11' (N : ℕ) (v : KanVar → ℝ) : |KanVar.x11' N v| ≤ |v .x11| := by
  unfold KanVar.x11'; split_ifs <;> simp
lemma abs_x21' (N : ℕ) (v : KanVar → ℝ) : |KanVar.x21' N v| ≤ |v .x21| := by
  unfold KanVar.x21'; split_ifs <;> simp
lemma abs_c' (N : ℕ) (v : KanVar → ℝ) : |KanVar.c' N v| ≤ |v .c| := by
  unfold KanVar.c'; split_ifs <;> simp

lemma abs_inv_sqrt_le (w : ℝ) : |(√w)⁻¹| ≤ 1 + |w⁻¹| := by
  have := inv_sqrt_le w; rwa [Real.norm_eq_abs] at this

lemma abs_inv_sqrt_mul (w1 w2 : ℝ) (hw : 0 ≤ w1) :
    |(√(w1 * w2))⁻¹| = |(√w1)⁻¹| * |(√w2)⁻¹| := by
  rw [Real.sqrt_mul hw, mul_inv, abs_mul]

lemma ratio_le_one (u z : ℝ) : |√u / √(z ^ 2 + u)| ≤ 1 := by
  rw [abs_of_nonneg (by positivity)]
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (z ^ 2 + u)) with h | h
  · rw [← h, div_zero]; norm_num
  · rw [div_le_one h]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg z])

lemma ratio_self_le_one (v : ℝ) : |√v / √v| ≤ 1 := by
  rcases eq_or_lt_of_le (Real.sqrt_nonneg v) with h | h
  · rw [← h]; simp
  · rw [div_self h.ne']; simp

lemma ratio_z_le_one (u z : ℝ) (hu : 0 ≤ u) : |z / √(z ^ 2 + u)| ≤ 1 := by
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (z ^ 2 + u)) with h | h
  · rw [← h, div_zero]; norm_num
  · rw [abs_div, abs_of_pos h, div_le_one h, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)

end KanAux

namespace KanAux
open RiskEU.OOSUVar ChiTest

lemma y1_bound (x11 x21 a b v2 w1 w2 : ℝ) (hw1 : 0 ≤ w1) (hv2 : 0 ≤ v2) :
    |x11 / √w1 + b * x21 / √(w1 * w2) + a * x21 / √(v2 * w2)| ≤
      |x11| * (1 + |w1⁻¹|) + |b| * |x21| * ((1 + |w1⁻¹|) * (1 + |w2⁻¹|)) +
        |a| * |x21| * ((1 + |v2⁻¹|) * (1 + |w2⁻¹|)) := by
  calc _ ≤ |x11 / √w1| + |b * x21 / √(w1 * w2)| + |a * x21 / √(v2 * w2)| := abs_add_three _ _ _
    _ = |x11| * |(√w1)⁻¹| + |b| * |x21| * (|(√w1)⁻¹| * |(√w2)⁻¹|) +
          |a| * |x21| * (|(√v2)⁻¹| * |(√w2)⁻¹|) := by
        simp only [div_eq_mul_inv, abs_mul, abs_inv_sqrt_mul _ _ hw1, abs_inv_sqrt_mul _ _ hv2]
    _ ≤ _ := by
        gcongr <;> exact abs_inv_sqrt_le _

/-- The `σ_g ψ` part of (IA47). -/
noncomputable def J1 (N : ℕ) (v : KanVar → ℝ) : ℝ :=
  √(v .v2) / √(v .z2 ^ 2 + v .u0) *
    (√(v .u0) * KanVar.y1 N v / √(v .v2) + v .a * v .z2 / v .v2)

noncomputable def J2 (N : ℕ) (v : KanVar → ℝ) : ℝ :=
  KanVar.x21' N v * √(v .u0) / √(v .w2) / v .v2

noncomputable def J3 (v : KanVar → ℝ) : ℝ := v .z2 / v .v2

lemma kanMeanRep_eq {N : ℕ} (M : Market N) (T : ℕ) (κ : ℝ) (v : KanVar → ℝ) :
    M.kanMeanRep T κ v = M.muG + (√M.sigmaG2 * √M.psi2) * J1 N v +
      (κ * √T * √M.psi2 / M.gamma) * J2 N v + (κ * √T * √M.psi2 / M.gamma) * J3 v := by
  unfold Market.kanMeanRep J1 J2 J3
  ring

lemma J1_bound (N : ℕ) (v : KanVar → ℝ) (hu : 0 ≤ v .u0) (hw1 : 0 ≤ v .w1) (hv2 : 0 ≤ v .v2) :
    |J1 N v| ≤ |v .x11| * (1 + |(v .w1)⁻¹|) +
      |v .b| * |v .x21| * ((1 + |(v .w1)⁻¹|) * (1 + |(v .w2)⁻¹|)) +
      |v .a| * |v .x21| * ((1 + |(v .v2)⁻¹|) * (1 + |(v .w2)⁻¹|)) + |v .a| * (1 + |(v .v2)⁻¹|) := by
  have e : J1 N v = (√(v .u0) / √(v .z2 ^ 2 + v .u0)) * (√(v .v2) / √(v .v2)) * KanVar.y1 N v +
      v .a * (v .z2 / √(v .z2 ^ 2 + v .u0)) * (√(v .v2) / v .v2) := by
    unfold J1; ring
  rw [e, Real.sqrt_div_self', one_div]
  have hy := y1_bound (KanVar.x11' N v) (KanVar.x21' N v) (v .a) (v .b) (v .v2) (v .w1) (v .w2) hw1 hv2
  have h1 := ratio_le_one (v .u0) (v .z2)
  have h2 := ratio_self_le_one (v .v2)
  have h3 := ratio_z_le_one (v .u0) (v .z2) hu
  have h4 := abs_inv_sqrt_le (v .v2)
  have hx11 := abs_x11' N v
  have hx21 := abs_x21' N v
  calc _ ≤ |√(v .u0) / √(v .z2 ^ 2 + v .u0)| * |√(v .v2) / √(v .v2)| * |KanVar.y1 N v| +
          |v .a| * |v .z2 / √(v .z2 ^ 2 + v .u0)| * |(√(v .v2))⁻¹| := by
        rw [← abs_mul, ← abs_mul, ← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ 1 * 1 * |KanVar.y1 N v| + |v .a| * 1 * (1 + |(v .v2)⁻¹|) := by gcongr
    _ ≤ _ := by
        simp only [one_mul, mul_one]
        unfold KanVar.y1
        have : |KanVar.x11' N v| * (1 + |(v .w1)⁻¹|) + |v .b| * |KanVar.x21' N v| *
            ((1 + |(v .w1)⁻¹|) * (1 + |(v .w2)⁻¹|)) + |v .a| * |KanVar.x21' N v| *
            ((1 + |(v .v2)⁻¹|) * (1 + |(v .w2)⁻¹|)) ≤ |v .x11| * (1 + |(v .w1)⁻¹|) +
            |v .b| * |v .x21| * ((1 + |(v .w1)⁻¹|) * (1 + |(v .w2)⁻¹|)) +
            |v .a| * |v .x21| * ((1 + |(v .v2)⁻¹|) * (1 + |(v .w2)⁻¹|)) := by gcongr
        linarith

lemma J2_bound (N : ℕ) (v : KanVar → ℝ) :
    |J2 N v| ≤ |v .x21| * (1 + |v .u0|) * (1 + |(v .w2)⁻¹|) * |(v .v2)⁻¹| := by
  unfold J2
  simp only [div_eq_mul_inv, abs_mul]
  have h2 := sqrt_le_one_add_abs (v .u0); rw [Real.norm_eq_abs] at h2
  have h1 := abs_x21' N v
  have h3 := abs_inv_sqrt_le (v .w2)
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply mul_le_mul _ h3 (abs_nonneg _) (by positivity)
  exact mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg _)

lemma J1_odd (N : ℕ) (v : KanVar → ℝ) :
    J1 N (fun i => if i ∈ ({.x11, .a, .b} : Finset KanVar) then -v i else v i) = - J1 N v := by
  unfold J1 KanVar.y1 KanVar.x11' KanVar.x21'
  simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, or_self, or_false, false_or,
    if_true, if_false]
  split_ifs <;> ring

lemma J2_odd (N : ℕ) (v : KanVar → ℝ) :
    J2 N (fun i => if i ∈ ({.x21} : Finset KanVar) then -v i else v i) = - J2 N v := by
  unfold J2 KanVar.x21'
  simp only [Finset.mem_singleton, reduceCtorEq, if_true, if_false]
  split_ifs <;> ring

lemma measurable_J1 (N : ℕ) : Measurable (J1 N) := by
  have := measurable_y1 N; unfold J1; fun_prop
lemma measurable_J2 (N : ℕ) : Measurable (J2 N) := by
  have := measurable_x21' N; unfold J2; fun_prop

end KanAux

namespace KanAux
open RiskEU.OOSUVar

/-- Transfer of moments through the Kan et al. representation. -/
lemma kan_transfer {N T : ℕ} (M : Market N) (hM : M.Standing T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin T → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r)
    (κ : ℝ) (hκ : κ ∈ Set.Icc (0 : ℝ) 1) (f : ℝ × ℝ → ℝ) (hf : Measurable f) :
    (Integrable (fun ω => f (M.oosMean κ (sampleData r ω), M.oosVar κ (sampleData r ω))) P ↔
      Integrable (fun v => f (M.kanMeanRep T κ v, M.kanVarRep T κ v))
        (Measure.pi (kanLaw N T M.psi2))) ∧
    ∫ ω, f (M.oosMean κ (sampleData r ω), M.oosVar κ (sampleData r ω)) ∂P =
      ∫ v, f (M.kanMeanRep T κ v, M.kanVarRep T κ v) ∂(Measure.pi (kanLaw N T M.psi2)) := by
  have hmap := kan_representation M hM P r hr κ hκ (Measure.pi (kanLaw N T M.psi2))
    (fun i (v : KanVar → ℝ) => v i) (canonical_isKan N T M.psi2)
  set F := fun ω => (M.oosMean κ (sampleData r ω), M.oosVar κ (sampleData r ω)) with hF
  set G := fun v : KanVar → ℝ => (M.kanMeanRep T κ v, M.kanVarRep T κ v) with hG
  have hGm : Measurable G := (measurable_kanMeanRep M T κ).prodMk (measurable_kanVarRep M T κ)
  change P.map F = (Measure.pi (kanLaw N T M.psi2)).map G at hmap
  have hFm : AEMeasurable F P := by
    apply aemeasurable_of_map_neZero
    rw [hmap]
    have : IsProbabilityMeasure ((Measure.pi (kanLaw N T M.psi2)).map G) :=
      Measure.isProbabilityMeasure_map hGm.aemeasurable
    infer_instance
  constructor
  · have h1 := integrable_map_measure hf.aestronglyMeasurable hFm
    rw [hmap, integrable_map_measure hf.aestronglyMeasurable hGm.aemeasurable] at h1
    exact h1.symm
  · rw [← integral_map hFm hf.aestronglyMeasurable, hmap,
      integral_map hGm.aemeasurable hf.aestronglyMeasurable]

end KanAux

namespace KanAux
open RiskEU.OOSUVar ChiTest

section
variable {N T : ℕ} {psi2 : ℝ}

lemma ae_nonneg_chi (i : KanVar) (k : ℕ) (h : kanLaw N T psi2 i = chiSq k) :
    ∀ᵐ v ∂(Measure.pi (kanLaw N T psi2)), 0 ≤ v i :=
  coord_ae i (p := fun x => 0 ≤ x) (by rw [h]; exact chiSq_ae_nonneg k)

lemma J1_integrable (hT : N + 7 < T) :
    Integrable (J1 N) (Measure.pi (kanLaw N T psi2)) := by
  have d1 : 2 < T - N + 1 := by omega
  have d2 : 2 < T - N + 2 := by omega
  have d3 : 2 < T - N + 3 := by omega
  set g1 : KanVar → ℝ → ℝ := Function.update (Function.update (fun _ _ => (1:ℝ))
    .x11 (fun x => |x|)) .w1 (fun x => 1 + |x⁻¹|)
  set g2 : KanVar → ℝ → ℝ := Function.update (Function.update (Function.update
    (Function.update (fun _ _ => (1:ℝ)) .b (fun x => |x|)) .x21 (fun x => |x|))
    .w1 (fun x => 1 + |x⁻¹|)) .w2 (fun x => 1 + |x⁻¹|)
  set g3 : KanVar → ℝ → ℝ := Function.update (Function.update (Function.update
    (Function.update (fun _ _ => (1:ℝ)) .a (fun x => |x|)) .x21 (fun x => |x|))
    .v2 (fun x => 1 + |x⁻¹|)) .w2 (fun x => 1 + |x⁻¹|)
  set g4 : KanVar → ℝ → ℝ := Function.update (Function.update (fun _ _ => (1:ℝ))
    .a (fun x => |x|)) .v2 (fun x => 1 + |x⁻¹|)
  have i1 := mono_integrable (N := N) (T := T) (psi2 := psi2) g1 (by
    intro i; cases i <;> simp only [g1, Function.update_apply, kanLaw, reduceCtorEq, if_true, if_false] <;>
      first | exact integrable_const _ | exact int_abs_gauss _ | exact int_one_add_abs_inv_chi d1 | exact int_one_add_abs_inv_chi d2 | exact int_one_add_abs_inv_chi d3)
  have i2 := mono_integrable (N := N) (T := T) (psi2 := psi2) g2 (by
    intro i; cases i <;> simp only [g2, Function.update_apply, kanLaw, reduceCtorEq, if_true, if_false] <;>
      first | exact integrable_const _ | exact int_abs_gauss _ | exact int_one_add_abs_inv_chi d1 | exact int_one_add_abs_inv_chi d2 | exact int_one_add_abs_inv_chi d3)
  have i3 := mono_integrable (N := N) (T := T) (psi2 := psi2) g3 (by
    intro i; cases i <;> simp only [g3, Function.update_apply, kanLaw, reduceCtorEq, if_true, if_false] <;>
      first | exact integrable_const _ | exact int_abs_gauss _ | exact int_one_add_abs_inv_chi d1 | exact int_one_add_abs_inv_chi d2 | exact int_one_add_abs_inv_chi d3)
  have i4 := mono_integrable (N := N) (T := T) (psi2 := psi2) g4 (by
    intro i; cases i <;> simp only [g4, Function.update_apply, kanLaw, reduceCtorEq, if_true, if_false] <;>
      first | exact integrable_const _ | exact int_abs_gauss _ | exact int_one_add_abs_inv_chi d1 | exact int_one_add_abs_inv_chi d2 | exact int_one_add_abs_inv_chi d3)
  refine (((i1.add i2).add i3).add i4).mono' (measurable_J1 N).aestronglyMeasurable ?_
  filter_upwards [ae_nonneg_chi .u0 (N - 2) rfl, ae_nonneg_chi .w1 (T - N + 3) rfl,
    ae_nonneg_chi .v2 (T - N + 1) rfl] with v hu hw hv
  rw [Real.norm_eq_abs]
  refine (J1_bound N v hu hw hv).trans (le_of_eq ?_)
  simp only [Pi.add_apply, prod_univ, g1, g2, g3, g4, Function.update]
  simp
  ring

lemma J2_integrable (hT : N + 7 < T) :
    Integrable (J2 N) (Measure.pi (kanLaw N T psi2)) := by
  have d1 : 2 < T - N + 1 := by omega
  have d2 : 2 < T - N + 2 := by omega
  set g : KanVar → ℝ → ℝ := Function.update (Function.update (Function.update
    (Function.update (fun _ _ => (1:ℝ)) .x21 (fun x => |x|)) .u0 (fun x => 1 + |x|))
    .w2 (fun x => 1 + |x⁻¹|)) .v2 (fun x => |x⁻¹|)
  have i := mono_integrable (N := N) (T := T) (psi2 := psi2) g (by
    intro i; cases i <;> simp only [g, Function.update_apply, kanLaw, reduceCtorEq, if_true, if_false] <;>
      first | exact integrable_const _ | exact int_abs_gauss _ | exact int_one_add_abs_inv_chi d2 | exact int_one_add_abs_chi _ | exact (int_inv_chi d1).abs)
  refine i.mono' (measurable_J2 N).aestronglyMeasurable (ae_of_all _ fun v => ?_)
  rw [Real.norm_eq_abs]
  refine (J2_bound N v).trans (le_of_eq ?_)
  simp only [prod_univ, g, Function.update]
  simp
  ring

lemma J3_integral (hT : N + 7 < T) :
    Integrable J3 (Measure.pi (kanLaw N T psi2)) ∧
    ∫ v, J3 v ∂(Measure.pi (kanLaw N T psi2)) = (√T * √psi2) * (1 / ((T : ℝ) - N - 1)) := by
  set g : KanVar → ℝ → ℝ := Function.update (Function.update (fun _ _ => (1:ℝ))
    .z2 (fun x => x)) .v2 (fun x => x⁻¹)
  have hJ : ∀ v : KanVar → ℝ, J3 v = ∏ i, g i (v i) := by
    intro v; simp only [prod_univ, g, Function.update]; simp [J3, div_eq_mul_inv]
  have d1 : 2 < T - N + 1 := by omega
  have hi : ∀ i, Integrable (g i) (kanLaw N T psi2 i) := by
    intro i; cases i <;> simp only [g, Function.update_apply, kanLaw, reduceCtorEq, if_true, if_false] <;>
      first | exact integrable_const _ | exact int_id_gauss _ | exact int_inv_chi d1
  refine ⟨(mono_integrable g hi).congr (ae_of_all _ fun v => (hJ v).symm), ?_⟩
  simp_rw [hJ]
  rw [mono_integral, prod_univ]
  simp only [g, Function.update]
  simp only [reduceCtorEq, dite_false, dite_true, integral_const, smul_eq_mul, mul_one,
    probReal_univ]
  have e1 : ∫ x, x ∂(kanLaw N T psi2 .z2) = √T * √psi2 := integral_id_gaussianReal
  have e2 : ∫ x, x⁻¹ ∂(kanLaw N T psi2 .v2) = 1 / ((T : ℝ) - N - 1) := by
    have := (chiSq_inv_moment (T - N + 1) 0 (by omega)).2
    simp only [zero_add, pow_one, Finset.range_one, Finset.prod_singleton, Nat.cast_zero,
      mul_zero, sub_zero] at this
    rw [show kanLaw N T psi2 .v2 = chiSq (T - N + 1) from rfl, this]
    congr 1
    have hNT : N ≤ T := by omega
    push_cast [Nat.cast_sub hNT]; ring
  simp [e1, e2]

end

end KanAux

open RiskEU.OOSUVar KanAux in
theorem solution {N T : ℕ} (M : Market N) (hM : M.Standing T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin T → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r)
    (κ : ℝ) (hκ : κ ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun ω => M.oosMean κ (sampleData r ω)) P ∧
    ∫ ω, M.oosMean κ (sampleData r ω) ∂P =
      M.muG + κ / M.gamma * ((T : ℝ) * M.psi2 / ((T : ℝ) - N - 1)) := by
  obtain ⟨hI, hE⟩ := kan_transfer M hM P r hr κ hκ (fun p => p.1) measurable_fst
  simp only at hI hE
  have hT : N + 7 < T := hM.2.1
  have hψ : 0 ≤ M.psi2 := psi2_nonneg M hM.2.2.1
  set μK := Measure.pi (kanLaw N T M.psi2)
  have i1 := J1_integrable (N := N) (T := T) (psi2 := M.psi2) hT
  have i2 := J2_integrable (N := N) (T := T) (psi2 := M.psi2) hT
  obtain ⟨i3, e3⟩ := J3_integral (N := N) (T := T) (psi2 := M.psi2) hT
  have hS1 : ∀ i ∈ ({.x11, .a, .b} : Finset KanVar), kanLaw N T M.psi2 i = gaussianReal 0 1 := by
    intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> rfl
  have hS2 : ∀ i ∈ ({.x21} : Finset KanVar), kanLaw N T M.psi2 i = gaussianReal 0 1 := by
    intro i hi; simp at hi; subst hi; rfl
  have e1 : ∫ v, J1 N v ∂μK = 0 := odd_integral_zero _ hS1 _ (measurable_J1 N) (J1_odd N)
  have e2 : ∫ v, J2 N v ∂μK = 0 := odd_integral_zero _ hS2 _ (measurable_J2 N) (J2_odd N)
  have hrep : (fun v => M.kanMeanRep T κ v) = fun v => M.muG + (√M.sigmaG2 * √M.psi2) * J1 N v +
      (κ * √T * √M.psi2 / M.gamma) * J2 N v + (κ * √T * √M.psi2 / M.gamma) * J3 v :=
    funext (kanMeanRep_eq M T κ)
  have iA : Integrable (fun v => M.muG + (√M.sigmaG2 * √M.psi2) * J1 N v) μK :=
    (integrable_const _).add (i1.const_mul _)
  have iB : Integrable (fun v => M.muG + (√M.sigmaG2 * √M.psi2) * J1 N v +
      (κ * √T * √M.psi2 / M.gamma) * J2 N v) μK := iA.add (i2.const_mul _)
  refine ⟨hI.2 (by rw [hrep]; exact iB.add (i3.const_mul _)), ?_⟩
  rw [hE, hrep, integral_add iB (i3.const_mul _), integral_add iA (i2.const_mul _),
    integral_add (integrable_const _) (i1.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const, e1, e2, e3]
  have hTN : (N : ℝ) + 7 < T := by exact_mod_cast hT
  have h1 : (T : ℝ) - N - 1 ≠ 0 := by intro h; linarith
  have hsT : √(T : ℝ) * √(T : ℝ) = T := Real.mul_self_sqrt (Nat.cast_nonneg T)
  have hsψ : √M.psi2 * √M.psi2 = M.psi2 := Real.mul_self_sqrt hψ
  simp only [probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero]
  have hγ : M.gamma ≠ 0 := hM.2.2.2.ne'
  congr 1
  calc κ * √T * √M.psi2 / M.gamma * (√T * √M.psi2 * (1 / ((T:ℝ) - N - 1)))
      = κ / M.gamma * ((√T * √T) * (√M.psi2 * √M.psi2) / ((T:ℝ) - N - 1)) := by
        field_simp
    _ = _ := by rw [hsT, hsψ]

