-- Prove2me | solution 1 for RiskEU.OOSUVar.eq_IA59
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T15:57:24.738474+00:00
-- url     : https://prove2.me/submissions/0a1ce02c-9cca-4989-80cd-ab0c89edaf80
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting
import Definitions.Def_RiskEU_OOSUVar_KanRepresentation
import Theorems.Thm_RiskEU_OOSUVar_kan_representation
import Theorems.Thm_RiskEU_OOSUVar_eq_IA49
import Theorems.Thm_RiskEU_OOSUVar_eq_IA51
import Theorems.Thm_RiskEU_OOSUVar_eq_IA52
import Theorems.Thm_RiskEU_OOSUVar_eq_IA53
import Theorems.Thm_RiskEU_OOSUVar_eq_IA54
import Theorems.Thm_RiskEU_OOSUVar_eq_IA55
import Theorems.Thm_RiskEU_OOSUVar_eq_IA56
import Theorems.Thm_RiskEU_OOSUVar_eq_IA57

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


namespace ChiTest

lemma gm_int_pow (m : ℝ) (n : ℕ) : Integrable (fun x : ℝ => x ^ n) (gaussianReal m 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := (memLp_id_gaussianReal (μ := m) (v := 1) (n : NNReal)).integrable_norm_pow (by positivity)
  refine h.mono' ?_ ?_
  · exact (by fun_prop : Measurable fun x : ℝ => x ^ n).aestronglyMeasurable
  · exact ae_of_all _ fun x => by simp [norm_pow]

lemma gm_moment (m : ℝ) (n : ℕ) :
    ∫ x, x ^ n ∂(gaussianReal m 1) = iteratedDeriv n (fun t : ℝ => rexp (m * t + t ^ 2 / 2)) 0 := by
  have := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal m 1) (by simp) n
  rw [mgf_fun_id_gaussianReal] at this
  simp only [NNReal.coe_one, one_mul] at this
  rw [this]; rfl

lemma gm_derivs (m : ℝ) :
    deriv (fun t : ℝ => rexp (m * t + t ^ 2 / 2)) = (fun t => (m + t) * rexp (m * t + t ^ 2 / 2)) ∧
    deriv (fun t : ℝ => (m + t) * rexp (m * t + t ^ 2 / 2)) =
      (fun t => (1 + (m + t) ^ 2) * rexp (m * t + t ^ 2 / 2)) ∧
    deriv (fun t : ℝ => (1 + (m + t) ^ 2) * rexp (m * t + t ^ 2 / 2)) =
      (fun t => (3 * (m + t) + (m + t) ^ 3) * rexp (m * t + t ^ 2 / 2)) ∧
    deriv (fun t : ℝ => (3 * (m + t) + (m + t) ^ 3) * rexp (m * t + t ^ 2 / 2)) =
      (fun t => (3 + 6 * (m + t) ^ 2 + (m + t) ^ 4) * rexp (m * t + t ^ 2 / 2)) := by
  have hE : ∀ t : ℝ, HasDerivAt (fun t : ℝ => rexp (m * t + t ^ 2 / 2))
      ((m + t) * rexp (m * t + t ^ 2 / 2)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => m * t + t ^ 2 / 2) (m + t) t :=
      (((hasDerivAt_id t).const_mul m).add ((hasDerivAt_pow 2 t).div_const 2)).congr_deriv
        (by norm_num <;> ring)
    exact h1.exp.congr_deriv (by ring)
  have hp : ∀ (P P' : ℝ → ℝ) (_ : ∀ t, HasDerivAt P (P' t) t) (t : ℝ),
      HasDerivAt (fun t => P t * rexp (m * t + t ^ 2 / 2))
        ((P' t + P t * (m + t)) * rexp (m * t + t ^ 2 / 2)) t := by
    intro P P' hP t
    exact ((hP t).mul (hE t)).congr_deriv (by ring)
  have d1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => m + t) 1 t := fun t =>
    ((hasDerivAt_id t).const_add m).congr_deriv (by norm_num)
  have d2 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => 1 + (m + t) ^ 2) (2 * (m + t)) t := fun t =>
    (((d1 t).pow 2).const_add 1).congr_deriv (by norm_num <;> ring)
  have d3 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => 3 * (m + t) + (m + t) ^ 3) (3 + 3 * (m + t) ^ 2) t :=
    fun t => (((d1 t).const_mul 3).add ((d1 t).pow 3)).congr_deriv (by norm_num <;> ring)
  refine ⟨funext fun t => (hE t).deriv, funext fun t => ?_, funext fun t => ?_, funext fun t => ?_⟩
  · rw [(hp _ _ d1 t).deriv]; ring
  · rw [(hp _ _ d2 t).deriv]; ring
  · rw [(hp _ _ d3 t).deriv]; ring

lemma gm_m1 (m : ℝ) : ∫ x, x ^ 1 ∂(gaussianReal m 1) = m := by
  rw [gm_moment, iteratedDeriv_one, (gm_derivs m).1]; simp
lemma gm_m2 (m : ℝ) : ∫ x, x ^ 2 ∂(gaussianReal m 1) = m ^ 2 + 1 := by
  rw [gm_moment, iteratedDeriv_succ, iteratedDeriv_one, (gm_derivs m).1, (gm_derivs m).2.1]; simp; ring
lemma gm_m3 (m : ℝ) : ∫ x, x ^ 3 ∂(gaussianReal m 1) = m ^ 3 + 3 * m := by
  rw [gm_moment, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, (gm_derivs m).1,
    (gm_derivs m).2.1, (gm_derivs m).2.2.1]; simp; ring
lemma gm_m4 (m : ℝ) : ∫ x, x ^ 4 ∂(gaussianReal m 1) = m ^ 4 + 6 * m ^ 2 + 3 := by
  rw [gm_moment, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one,
    (gm_derivs m).1, (gm_derivs m).2.1, (gm_derivs m).2.2.1, (gm_derivs m).2.2.2]; simp; ring

lemma chi_inv_int (k p : ℕ) (hk : 2 * p + 2 < k) :
    Integrable (fun x : ℝ => (x ^ (p + 1))⁻¹) (RiskEU.OOSUVar.chiSq k) := (chiSq_inv_moment k p hk).1
lemma chi_inv_val (k p : ℕ) (hk : 2 * p + 2 < k) :
    ∫ x, (x ^ (p + 1))⁻¹ ∂(RiskEU.OOSUVar.chiSq k) =
      1 / ∏ i ∈ Finset.range (p + 1), ((k : ℝ) - 2 - 2 * i) := (chiSq_inv_moment k p hk).2

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


namespace KanAux
open RiskEU.OOSUVar ChiTest

noncomputable def f3 (N : ℕ) (x : ℝ) : ℝ := if 3 ≤ N then x else 0
noncomputable def f4 (N : ℕ) (x : ℝ) : ℝ := if 4 ≤ N then x else 0
lemma x11'_eq (N : ℕ) (v : KanVar → ℝ) : KanVar.x11' N v = f3 N (v .x11) := rfl
lemma x21'_eq (N : ℕ) (v : KanVar → ℝ) : KanVar.x21' N v = f3 N (v .x21) := rfl
lemma c'_eq (N : ℕ) (v : KanVar → ℝ) : KanVar.c' N v = f4 N (v .c) := rfl
lemma f3_neg (N : ℕ) (x : ℝ) : f3 N (-x) = - f3 N x := by unfold f3; split_ifs <;> simp
lemma f4_neg (N : ℕ) (x : ℝ) : f4 N (-x) = - f4 N x := by unfold f4; split_ifs <;> simp
lemma measurable_f3 (N : ℕ) : Measurable (f3 N) := by unfold f3; split_ifs <;> fun_prop
lemma measurable_f4 (N : ℕ) : Measurable (f4 N) := by unfold f4; split_ifs <;> fun_prop

/-- Coordinate functions packaged by variable. -/
def M12 (gz2 gu0 gv2 gw1 gw2 gs1 gs2 gx11 gx21 ga gb gc : ℝ → ℝ) : KanVar → ℝ → ℝ
  | .z2 => gz2 | .u0 => gu0 | .v2 => gv2 | .w1 => gw1 | .w2 => gw2 | .s1 => gs1
  | .s2 => gs2 | .x11 => gx11 | .x21 => gx21 | .a => ga | .b => gb | .c => gc

def one : ℝ → ℝ := fun _ => 1

section
variable {N T : ℕ} {psi2 : ℝ}

lemma M12_spec (gz2 gu0 gv2 gw1 gw2 gs1 gs2 gx11 gx21 ga gb gc : ℝ → ℝ)
    (hz2 : Integrable gz2 (kanLaw N T psi2 .z2)) (hu0 : Integrable gu0 (kanLaw N T psi2 .u0))
    (hv2 : Integrable gv2 (kanLaw N T psi2 .v2)) (hw1 : Integrable gw1 (kanLaw N T psi2 .w1))
    (hw2 : Integrable gw2 (kanLaw N T psi2 .w2)) (hs1 : Integrable gs1 (kanLaw N T psi2 .s1))
    (hs2 : Integrable gs2 (kanLaw N T psi2 .s2)) (hx11 : Integrable gx11 (kanLaw N T psi2 .x11))
    (hx21 : Integrable gx21 (kanLaw N T psi2 .x21)) (ha : Integrable ga (kanLaw N T psi2 .a))
    (hb : Integrable gb (kanLaw N T psi2 .b)) (hc : Integrable gc (kanLaw N T psi2 .c)) :
    Integrable (fun v : KanVar → ℝ => gz2 (v .z2) * gu0 (v .u0) * gv2 (v .v2) * gw1 (v .w1) *
      gw2 (v .w2) * gs1 (v .s1) * gs2 (v .s2) * gx11 (v .x11) * gx21 (v .x21) * ga (v .a) *
      gb (v .b) * gc (v .c)) (Measure.pi (kanLaw N T psi2)) ∧
    ∫ v, gz2 (v .z2) * gu0 (v .u0) * gv2 (v .v2) * gw1 (v .w1) *
      gw2 (v .w2) * gs1 (v .s1) * gs2 (v .s2) * gx11 (v .x11) * gx21 (v .x21) * ga (v .a) *
      gb (v .b) * gc (v .c) ∂(Measure.pi (kanLaw N T psi2)) =
    (∫ x, gz2 x ∂(kanLaw N T psi2 .z2)) * (∫ x, gu0 x ∂(kanLaw N T psi2 .u0)) *
      (∫ x, gv2 x ∂(kanLaw N T psi2 .v2)) * (∫ x, gw1 x ∂(kanLaw N T psi2 .w1)) *
      (∫ x, gw2 x ∂(kanLaw N T psi2 .w2)) * (∫ x, gs1 x ∂(kanLaw N T psi2 .s1)) *
      (∫ x, gs2 x ∂(kanLaw N T psi2 .s2)) * (∫ x, gx11 x ∂(kanLaw N T psi2 .x11)) *
      (∫ x, gx21 x ∂(kanLaw N T psi2 .x21)) * (∫ x, ga x ∂(kanLaw N T psi2 .a)) *
      (∫ x, gb x ∂(kanLaw N T psi2 .b)) * (∫ x, gc x ∂(kanLaw N T psi2 .c)) := by
  set g := M12 gz2 gu0 gv2 gw1 gw2 gs1 gs2 gx11 gx21 ga gb gc
  have hi : ∀ i, Integrable (g i) (kanLaw N T psi2 i) := by
    intro i; cases i <;> assumption
  have hp : ∀ v : KanVar → ℝ, ∏ i, g i (v i) = gz2 (v .z2) * gu0 (v .u0) * gv2 (v .v2) *
      gw1 (v .w1) * gw2 (v .w2) * gs1 (v .s1) * gs2 (v .s2) * gx11 (v .x11) * gx21 (v .x21) *
      ga (v .a) * gb (v .b) * gc (v .c) := fun v => by rw [prod_univ]; rfl
  refine ⟨(mono_integrable g hi).congr (ae_of_all _ fun v => hp v), ?_⟩
  simp_rw [← hp]
  rw [mono_integral, prod_univ]
  rfl

lemma int_one (μ : Measure ℝ) [IsProbabilityMeasure μ] : Integrable one μ := integrable_const _
lemma I_one (μ : Measure ℝ) [IsProbabilityMeasure μ] : ∫ x, one x ∂μ = 1 := by simp [one]

end

lemma int_f3sq (N : ℕ) : Integrable (fun x => f3 N x ^ 2) (gaussianReal 0 1) := by
  unfold f3; split_ifs
  · exact int_sq_gauss 0
  · simp
lemma I_f3sq (N : ℕ) : ∫ x, f3 N x ^ 2 ∂(gaussianReal 0 1) = if 3 ≤ N then 1 else 0 := by
  unfold f3; split_ifs
  · exact gauss_moment2
  · simp
lemma int_f4sq (N : ℕ) : Integrable (fun x => f4 N x ^ 2) (gaussianReal 0 1) := by
  unfold f4; split_ifs
  · exact int_sq_gauss 0
  · simp
lemma I_f4sq (N : ℕ) : ∫ x, f4 N x ^ 2 ∂(gaussianReal 0 1) = if 4 ≤ N then 1 else 0 := by
  unfold f4; split_ifs
  · exact gauss_moment2
  · simp
lemma int_f3_4 (N : ℕ) : Integrable (fun x => f3 N x ^ 4) (gaussianReal 0 1) := by
  unfold f3; split_ifs
  · exact gauss_int_pow 4
  · simp
lemma I_sq0 : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := gauss_moment2
lemma I_inv {k : ℕ} (hk : 2 < k) : ∫ x, x⁻¹ ∂(chiSq k) = 1 / ((k : ℝ) - 2) := by
  have := (chiSq_inv_moment k 0 (by omega)).2
  simpa using this
lemma I_inv2 {k : ℕ} (hk : 4 < k) : ∫ x, (x ^ 2)⁻¹ ∂(chiSq k) = 1 / (((k : ℝ) - 2) * ((k : ℝ) - 4)) := by
  have := (chiSq_inv_moment k 1 (by omega)).2
  simp [Finset.prod_range_succ] at this
  rw [this, one_div, mul_inv, mul_comm]; ring_nf
lemma I_id_chi (k : ℕ) : ∫ x, x ∂(chiSq k) = k := (chiSq_moment1 k).2
lemma int_id_chi (k : ℕ) : Integrable (fun x : ℝ => x) (chiSq k) := (chiSq_moment1 k).1
lemma int_sq_chi (k : ℕ) : Integrable (fun x : ℝ => x ^ 2) (chiSq k) := (chiSq_moment2 k).1
lemma I_sq_gauss (m : ℝ) : ∫ x, x ^ 2 ∂(gaussianReal m 1) = m ^ 2 + 1 := by
  have h := variance_eq_sub (μ := gaussianReal m 1) (X := id) (memLp_id_gaussianReal 2)
  rw [variance_id_gaussianReal] at h
  have e : ∫ x, x ∂(gaussianReal m 1) = m := integral_id_gaussianReal
  simp only [Pi.pow_apply, id] at h
  rw [e] at h
  push_cast at h
  linarith

lemma memLp2_of_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f G : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hG : Integrable G μ) (h : ∀ᵐ x ∂μ, f x ^ 2 = G x) :
    MemLp f 2 μ :=
  (memLp_two_iff_integrable_sq hf).2 (hG.congr (h.mono fun x hx => hx.symm))

end KanAux

namespace KanAux
open RiskEU.OOSUVar ChiTest

section
variable {N T : ℕ} {psi2 : ℝ}

lemma m1 (hT : N + 7 < T) :
    Integrable (fun v : KanVar → ℝ => (v .w1)⁻¹ * f3 N (v .x11) ^ 2) (Measure.pi (kanLaw N T psi2)) ∧
    ∫ v, (v .w1)⁻¹ * f3 N (v .x11) ^ 2 ∂(Measure.pi (kanLaw N T psi2)) = (1 / ((((T - N + 3 : ℕ) : ℝ)) - 2)) * (if 3 ≤ N then (1:ℝ) else 0) := by
  obtain ⟨hi, he⟩ := M12_spec (N := N) (T := T) (psi2 := psi2) one one one (fun x => x⁻¹) one one one (fun x => f3 N x ^ 2) one one one one
    (int_one _) (int_one _) (int_one _) (int_inv_chi (show 2 < T - N + 3 by omega)) (int_one _) (int_one _) (int_one _) (int_f3sq N) (int_one _) (int_one _) (int_one _) (int_one _)
  have ef : (fun v : KanVar → ℝ => one (v .z2) * one (v .u0) * one (v .v2) * ((fun x => x⁻¹)) (v .w1) * one (v .w2) * one (v .s1) * one (v .s2) * ((fun x => f3 N x ^ 2)) (v .x11) * one (v .x21) * one (v .a) * one (v .b) * one (v .c)) = fun v => (v .w1)⁻¹ * f3 N (v .x11) ^ 2 := by
    funext v; simp only [one]; ring
  rw [ef] at hi he
  refine ⟨hi, ?_⟩
  rw [he]
  simp only [I_one]
  simp only [kanLaw]
  rw [I_inv (show 2 < T - N + 3 by omega)]
  rw [I_f3sq N]
  ring

lemma m2 (hT : N + 7 < T) :
    Integrable (fun v : KanVar → ℝ => (v .w1)⁻¹ * (v .w2)⁻¹ * f3 N (v .x21) ^ 2 * (v .b) ^ 2) (Measure.pi (kanLaw N T psi2)) ∧
    ∫ v, (v .w1)⁻¹ * (v .w2)⁻¹ * f3 N (v .x21) ^ 2 * (v .b) ^ 2 ∂(Measure.pi (kanLaw N T psi2)) = (1 / ((((T - N + 3 : ℕ) : ℝ)) - 2)) * (1 / ((((T - N + 2 : ℕ) : ℝ)) - 2)) * (if 3 ≤ N then (1:ℝ) else 0) * (1:ℝ) := by
  obtain ⟨hi, he⟩ := M12_spec (N := N) (T := T) (psi2 := psi2) one one one (fun x => x⁻¹) (fun x => x⁻¹) one one one (fun x => f3 N x ^ 2) one (fun x => x ^ 2) one
    (int_one _) (int_one _) (int_one _) (int_inv_chi (show 2 < T - N + 3 by omega)) (int_inv_chi (show 2 < T - N + 2 by omega)) (int_one _) (int_one _) (int_one _) (int_f3sq N) (int_one _) (int_sq_gauss 0) (int_one _)
  have ef : (fun v : KanVar → ℝ => one (v .z2) * one (v .u0) * one (v .v2) * ((fun x => x⁻¹)) (v .w1) * ((fun x => x⁻¹)) (v .w2) * one (v .s1) * one (v .s2) * one (v .x11) * ((fun x => f3 N x ^ 2)) (v .x21) * one (v .a) * ((fun x => x ^ 2)) (v .b) * one (v .c)) = fun v => (v .w1)⁻¹ * (v .w2)⁻¹ * f3 N (v .x21) ^ 2 * (v .b) ^ 2 := by
    funext v; simp only [one]; ring
  rw [ef] at hi he
  refine ⟨hi, ?_⟩
  rw [he]
  simp only [I_one]
  simp only [kanLaw]
  rw [I_inv (show 2 < T - N + 3 by omega)]
  rw [I_inv (show 2 < T - N + 2 by omega)]
  rw [I_f3sq N]
  rw [I_sq0]
  ring

lemma m3 (hT : N + 7 < T) :
    Integrable (fun v : KanVar → ℝ => (v .v2)⁻¹ * (v .w2)⁻¹ * f3 N (v .x21) ^ 2 * (v .a) ^ 2) (Measure.pi (kanLaw N T psi2)) ∧
    ∫ v, (v .v2)⁻¹ * (v .w2)⁻¹ * f3 N (v .x21) ^ 2 * (v .a) ^ 2 ∂(Measure.pi (kanLaw N T psi2)) = (1 / ((((T - N + 1 : ℕ) : ℝ)) - 2)) * (1 / ((((T - N + 2 : ℕ) : ℝ)) - 2)) * (if 3 ≤ N then (1:ℝ) else 0) * (1:ℝ) := by
  obtain ⟨hi, he⟩ := M12_spec (N := N) (T := T) (psi2 := psi2) one one (fun x => x⁻¹) one (fun x => x⁻¹) one one one (fun x => f3 N x ^ 2) (fun x => x ^ 2) one one
    (int_one _) (int_one _) (int_inv_chi (show 2 < T - N + 1 by omega)) (int_one _) (int_inv_chi (show 2 < T - N + 2 by omega)) (int_one _) (int_one _) (int_one _) (int_f3sq N) (int_sq_gauss 0) (int_one _) (int_one _)
  have ef : (fun v : KanVar → ℝ => one (v .z2) * one (v .u0) * ((fun x => x⁻¹)) (v .v2) * one (v .w1) * ((fun x => x⁻¹)) (v .w2) * one (v .s1) * one (v .s2) * one (v .x11) * ((fun x => f3 N x ^ 2)) (v .x21) * ((fun x => x ^ 2)) (v .a) * one (v .b) * one (v .c)) = fun v => (v .v2)⁻¹ * (v .w2)⁻¹ * f3 N (v .x21) ^ 2 * (v .a) ^ 2 := by
    funext v; simp only [one]; ring
  rw [ef] at hi he
  refine ⟨hi, ?_⟩
  rw [he]
  simp only [I_one]
  simp only [kanLaw]
  rw [I_inv (show 2 < T - N + 1 by omega)]
  rw [I_inv (show 2 < T - N + 2 by omega)]
  rw [I_f3sq N]
  rw [I_sq0]
  ring

lemma m4 (hT : N + 7 < T) :
    Integrable (fun v : KanVar → ℝ => (v .w1)⁻¹ * f4 N (v .c) ^ 2) (Measure.pi (kanLaw N T psi2)) ∧
    ∫ v, (v .w1)⁻¹ * f4 N (v .c) ^ 2 ∂(Measure.pi (kanLaw N T psi2)) = (1 / ((((T - N + 3 : ℕ) : ℝ)) - 2)) * (if 4 ≤ N then (1:ℝ) else 0) := by
  obtain ⟨hi, he⟩ := M12_spec (N := N) (T := T) (psi2 := psi2) one one one (fun x => x⁻¹) one one one one one one one (fun x => f4 N x ^ 2)
    (int_one _) (int_one _) (int_one _) (int_inv_chi (show 2 < T - N + 3 by omega)) (int_one _) (int_one _) (int_one _) (int_one _) (int_one _) (int_one _) (int_one _) (int_f4sq N)
  have ef : (fun v : KanVar → ℝ => one (v .z2) * one (v .u0) * one (v .v2) * ((fun x => x⁻¹)) (v .w1) * one (v .w2) * one (v .s1) * one (v .s2) * one (v .x11) * one (v .x21) * one (v .a) * one (v .b) * ((fun x => f4 N x ^ 2)) (v .c)) = fun v => (v .w1)⁻¹ * f4 N (v .c) ^ 2 := by
    funext v; simp only [one]; ring
  rw [ef] at hi he
  refine ⟨hi, ?_⟩
  rw [he]
  simp only [I_one]
  simp only [kanLaw]
  rw [I_inv (show 2 < T - N + 3 by omega)]
  rw [I_f4sq N]
  ring

lemma m5 (hT : N + 7 < T) :
    Integrable (fun v : KanVar → ℝ => (v .w1)⁻¹ * (v .w2)⁻¹ * v .s2 * (v .b) ^ 2) (Measure.pi (kanLaw N T psi2)) ∧
    ∫ v, (v .w1)⁻¹ * (v .w2)⁻¹ * v .s2 * (v .b) ^ 2 ∂(Measure.pi (kanLaw N T psi2)) = (1 / ((((T - N + 3 : ℕ) : ℝ)) - 2)) * (1 / ((((T - N + 2 : ℕ) : ℝ)) - 2)) * (((N - 3 : ℕ) : ℝ)) * (1:ℝ) := by
  obtain ⟨hi, he⟩ := M12_spec (N := N) (T := T) (psi2 := psi2) one one one (fun x => x⁻¹) (fun x => x⁻¹) one (fun x => x) one one one (fun x => x ^ 2) one
    (int_one _) (int_one _) (int_one _) (int_inv_chi (show 2 < T - N + 3 by omega)) (int_inv_chi (show 2 < T - N + 2 by omega)) (int_one _) (int_id_chi (N - 3)) (int_one _) (int_one _) (int_one _) (int_sq_gauss 0) (int_one _)
  have ef : (fun v : KanVar → ℝ => one (v .z2) * one (v .u0) * one (v .v2) * ((fun x => x⁻¹)) (v .w1) * ((fun x => x⁻¹)) (v .w2) * one (v .s1) * ((fun x => x)) (v .s2) * one (v .x11) * one (v .x21) * one (v .a) * ((fun x => x ^ 2)) (v .b) * one (v .c)) = fun v => (v .w1)⁻¹ * (v .w2)⁻¹ * v .s2 * (v .b) ^ 2 := by
    funext v; simp only [one]; ring
  rw [ef] at hi he
  refine ⟨hi, ?_⟩
  rw [he]
  simp only [I_one]
  simp only [kanLaw]
  rw [I_inv (show 2 < T - N + 3 by omega)]
  rw [I_inv (show 2 < T - N + 2 by omega)]
  rw [I_id_chi (N - 3)]
  rw [I_sq0]
  ring

lemma m6 (hT : N + 7 < T) :
    Integrable (fun v : KanVar → ℝ => (v .v2)⁻¹ * (v .w2)⁻¹ * v .s2 * (v .a) ^ 2) (Measure.pi (kanLaw N T psi2)) ∧
    ∫ v, (v .v2)⁻¹ * (v .w2)⁻¹ * v .s2 * (v .a) ^ 2 ∂(Measure.pi (kanLaw N T psi2)) = (1 / ((((T - N + 1 : ℕ) : ℝ)) - 2)) * (1 / ((((T - N + 2 : ℕ) : ℝ)) - 2)) * (((N - 3 : ℕ) : ℝ)) * (1:ℝ) := by
  obtain ⟨hi, he⟩ := M12_spec (N := N) (T := T) (psi2 := psi2) one one (fun x => x⁻¹) one (fun x => x⁻¹) one (fun x => x) one one (fun x => x ^ 2) one one
    (int_one _) (int_one _) (int_inv_chi (show 2 < T - N + 1 by omega)) (int_one _) (int_inv_chi (show 2 < T - N + 2 by omega)) (int_one _) (int_id_chi (N - 3)) (int_one _) (int_one _) (int_sq_gauss 0) (int_one _) (int_one _)
  have ef : (fun v : KanVar → ℝ => one (v .z2) * one (v .u0) * ((fun x => x⁻¹)) (v .v2) * one (v .w1) * ((fun x => x⁻¹)) (v .w2) * one (v .s1) * ((fun x => x)) (v .s2) * one (v .x11) * one (v .x21) * ((fun x => x ^ 2)) (v .a) * one (v .b) * one (v .c)) = fun v => (v .v2)⁻¹ * (v .w2)⁻¹ * v .s2 * (v .a) ^ 2 := by
    funext v; simp only [one]; ring
  rw [ef] at hi he
  refine ⟨hi, ?_⟩
  rw [he]
  simp only [I_one]
  simp only [kanLaw]
  rw [I_inv (show 2 < T - N + 1 by omega)]
  rw [I_inv (show 2 < T - N + 2 by omega)]
  rw [I_id_chi (N - 3)]
  rw [I_sq0]
  ring

lemma m7 (hT : N + 7 < T) :
    Integrable (fun v : KanVar → ℝ => (v .w1)⁻¹ * v .s1) (Measure.pi (kanLaw N T psi2)) ∧
    ∫ v, (v .w1)⁻¹ * v .s1 ∂(Measure.pi (kanLaw N T psi2)) = (1 / ((((T - N + 3 : ℕ) : ℝ)) - 2)) * (((N - 4 : ℕ) : ℝ)) := by
  obtain ⟨hi, he⟩ := M12_spec (N := N) (T := T) (psi2 := psi2) one one one (fun x => x⁻¹) one (fun x => x) one one one one one one
    (int_one _) (int_one _) (int_one _) (int_inv_chi (show 2 < T - N + 3 by omega)) (int_one _) (int_id_chi (N - 4)) (int_one _) (int_one _) (int_one _) (int_one _) (int_one _) (int_one _)
  have ef : (fun v : KanVar → ℝ => one (v .z2) * one (v .u0) * one (v .v2) * ((fun x => x⁻¹)) (v .w1) * one (v .w2) * ((fun x => x)) (v .s1) * one (v .s2) * one (v .x11) * one (v .x21) * one (v .a) * one (v .b) * one (v .c)) = fun v => (v .w1)⁻¹ * v .s1 := by
    funext v; simp only [one]; ring
  rw [ef] at hi he
  refine ⟨hi, ?_⟩
  rw [he]
  simp only [I_one]
  simp only [kanLaw]
  rw [I_inv (show 2 < T - N + 3 by omega)]
  rw [I_id_chi (N - 4)]
  ring

lemma m8 (hT : N + 7 < T) :
    Integrable (fun v : KanVar → ℝ => (v .v2)⁻¹ * (v .a) ^ 2) (Measure.pi (kanLaw N T psi2)) ∧
    ∫ v, (v .v2)⁻¹ * (v .a) ^ 2 ∂(Measure.pi (kanLaw N T psi2)) = (1 / ((((T - N + 1 : ℕ) : ℝ)) - 2)) * (1:ℝ) := by
  obtain ⟨hi, he⟩ := M12_spec (N := N) (T := T) (psi2 := psi2) one one (fun x => x⁻¹) one one one one one one (fun x => x ^ 2) one one
    (int_one _) (int_one _) (int_inv_chi (show 2 < T - N + 1 by omega)) (int_one _) (int_one _) (int_one _) (int_one _) (int_one _) (int_one _) (int_sq_gauss 0) (int_one _) (int_one _)
  have ef : (fun v : KanVar → ℝ => one (v .z2) * one (v .u0) * ((fun x => x⁻¹)) (v .v2) * one (v .w1) * one (v .w2) * one (v .s1) * one (v .s2) * one (v .x11) * one (v .x21) * ((fun x => x ^ 2)) (v .a) * one (v .b) * one (v .c)) = fun v => (v .v2)⁻¹ * (v .a) ^ 2 := by
    funext v; simp only [one]; ring
  rw [ef] at hi he
  refine ⟨hi, ?_⟩
  rw [he]
  simp only [I_one]
  simp only [kanLaw]
  rw [I_inv (show 2 < T - N + 1 by omega)]
  rw [I_sq0]
  ring

lemma m9 (hT : N + 7 < T) :
    Integrable (fun v : KanVar → ℝ => (v .z2) ^ 2 * ((v .v2) ^ 2)⁻¹) (Measure.pi (kanLaw N T psi2)) ∧
    ∫ v, (v .z2) ^ 2 * ((v .v2) ^ 2)⁻¹ ∂(Measure.pi (kanLaw N T psi2)) = ((√(T:ℝ) * √psi2) ^ 2 + 1) * (1 / ((((T - N + 1 : ℕ) : ℝ) - 2) * (((T - N + 1 : ℕ) : ℝ) - 4))) := by
  obtain ⟨hi, he⟩ := M12_spec (N := N) (T := T) (psi2 := psi2) (fun x => x ^ 2) one (fun x => (x ^ 2)⁻¹) one one one one one one one one one
    (int_sq_gauss _) (int_one _) (int_inv2_chi (show 4 < T - N + 1 by omega)) (int_one _) (int_one _) (int_one _) (int_one _) (int_one _) (int_one _) (int_one _) (int_one _) (int_one _)
  have ef : (fun v : KanVar → ℝ => ((fun x => x ^ 2)) (v .z2) * one (v .u0) * ((fun x => (x ^ 2)⁻¹)) (v .v2) * one (v .w1) * one (v .w2) * one (v .s1) * one (v .s2) * one (v .x11) * one (v .x21) * one (v .a) * one (v .b) * one (v .c)) = fun v => (v .z2) ^ 2 * ((v .v2) ^ 2)⁻¹ := by
    funext v; simp only [one]; ring
  rw [ef] at hi he
  refine ⟨hi, ?_⟩
  rw [he]
  simp only [I_one]
  simp only [kanLaw]
  rw [I_sq_gauss _]
  rw [I_inv2 (show 4 < T - N + 1 by omega)]
  ring

lemma m10 (hT : N + 7 < T) :
    Integrable (fun v : KanVar → ℝ => v .u0 * ((v .v2) ^ 2)⁻¹) (Measure.pi (kanLaw N T psi2)) ∧
    ∫ v, v .u0 * ((v .v2) ^ 2)⁻¹ ∂(Measure.pi (kanLaw N T psi2)) = (((N - 2 : ℕ) : ℝ)) * (1 / ((((T - N + 1 : ℕ) : ℝ) - 2) * (((T - N + 1 : ℕ) : ℝ) - 4))) := by
  obtain ⟨hi, he⟩ := M12_spec (N := N) (T := T) (psi2 := psi2) one (fun x => x) (fun x => (x ^ 2)⁻¹) one one one one one one one one one
    (int_one _) (int_id_chi (N - 2)) (int_inv2_chi (show 4 < T - N + 1 by omega)) (int_one _) (int_one _) (int_one _) (int_one _) (int_one _) (int_one _) (int_one _) (int_one _) (int_one _)
  have ef : (fun v : KanVar → ℝ => one (v .z2) * ((fun x => x)) (v .u0) * ((fun x => (x ^ 2)⁻¹)) (v .v2) * one (v .w1) * one (v .w2) * one (v .s1) * one (v .s2) * one (v .x11) * one (v .x21) * one (v .a) * one (v .b) * one (v .c)) = fun v => v .u0 * ((v .v2) ^ 2)⁻¹ := by
    funext v; simp only [one]; ring
  rw [ef] at hi he
  refine ⟨hi, ?_⟩
  rw [he]
  simp only [I_one]
  simp only [kanLaw]
  rw [I_id_chi (N - 2)]
  rw [I_inv2 (show 4 < T - N + 1 by omega)]
  ring

lemma m11 (hT : N + 7 < T) :
    Integrable (fun v : KanVar → ℝ => (v .z2) ^ 2 * ((v .v2) ^ 2)⁻¹ * (v .w2)⁻¹ * f3 N (v .x21) ^ 2) (Measure.pi (kanLaw N T psi2)) ∧
    ∫ v, (v .z2) ^ 2 * ((v .v2) ^ 2)⁻¹ * (v .w2)⁻¹ * f3 N (v .x21) ^ 2 ∂(Measure.pi (kanLaw N T psi2)) = ((√(T:ℝ) * √psi2) ^ 2 + 1) * (1 / ((((T - N + 1 : ℕ) : ℝ) - 2) * (((T - N + 1 : ℕ) : ℝ) - 4))) * (1 / ((((T - N + 2 : ℕ) : ℝ)) - 2)) * (if 3 ≤ N then (1:ℝ) else 0) := by
  obtain ⟨hi, he⟩ := M12_spec (N := N) (T := T) (psi2 := psi2) (fun x => x ^ 2) one (fun x => (x ^ 2)⁻¹) one (fun x => x⁻¹) one one one (fun x => f3 N x ^ 2) one one one
    (int_sq_gauss _) (int_one _) (int_inv2_chi (show 4 < T - N + 1 by omega)) (int_one _) (int_inv_chi (show 2 < T - N + 2 by omega)) (int_one _) (int_one _) (int_one _) (int_f3sq N) (int_one _) (int_one _) (int_one _)
  have ef : (fun v : KanVar → ℝ => ((fun x => x ^ 2)) (v .z2) * one (v .u0) * ((fun x => (x ^ 2)⁻¹)) (v .v2) * one (v .w1) * ((fun x => x⁻¹)) (v .w2) * one (v .s1) * one (v .s2) * one (v .x11) * ((fun x => f3 N x ^ 2)) (v .x21) * one (v .a) * one (v .b) * one (v .c)) = fun v => (v .z2) ^ 2 * ((v .v2) ^ 2)⁻¹ * (v .w2)⁻¹ * f3 N (v .x21) ^ 2 := by
    funext v; simp only [one]; ring
  rw [ef] at hi he
  refine ⟨hi, ?_⟩
  rw [he]
  simp only [I_one]
  simp only [kanLaw]
  rw [I_sq_gauss _]
  rw [I_inv2 (show 4 < T - N + 1 by omega)]
  rw [I_inv (show 2 < T - N + 2 by omega)]
  rw [I_f3sq N]
  ring

lemma m12 (hT : N + 7 < T) :
    Integrable (fun v : KanVar → ℝ => (v .z2) ^ 2 * ((v .v2) ^ 2)⁻¹ * (v .w2)⁻¹ * v .s2) (Measure.pi (kanLaw N T psi2)) ∧
    ∫ v, (v .z2) ^ 2 * ((v .v2) ^ 2)⁻¹ * (v .w2)⁻¹ * v .s2 ∂(Measure.pi (kanLaw N T psi2)) = ((√(T:ℝ) * √psi2) ^ 2 + 1) * (1 / ((((T - N + 1 : ℕ) : ℝ) - 2) * (((T - N + 1 : ℕ) : ℝ) - 4))) * (1 / ((((T - N + 2 : ℕ) : ℝ)) - 2)) * (((N - 3 : ℕ) : ℝ)) := by
  obtain ⟨hi, he⟩ := M12_spec (N := N) (T := T) (psi2 := psi2) (fun x => x ^ 2) one (fun x => (x ^ 2)⁻¹) one (fun x => x⁻¹) one (fun x => x) one one one one one
    (int_sq_gauss _) (int_one _) (int_inv2_chi (show 4 < T - N + 1 by omega)) (int_one _) (int_inv_chi (show 2 < T - N + 2 by omega)) (int_one _) (int_id_chi (N - 3)) (int_one _) (int_one _) (int_one _) (int_one _) (int_one _)
  have ef : (fun v : KanVar → ℝ => ((fun x => x ^ 2)) (v .z2) * one (v .u0) * ((fun x => (x ^ 2)⁻¹)) (v .v2) * one (v .w1) * ((fun x => x⁻¹)) (v .w2) * one (v .s1) * ((fun x => x)) (v .s2) * one (v .x11) * one (v .x21) * one (v .a) * one (v .b) * one (v .c)) = fun v => (v .z2) ^ 2 * ((v .v2) ^ 2)⁻¹ * (v .w2)⁻¹ * v .s2 := by
    funext v; simp only [one]; ring
  rw [ef] at hi he
  refine ⟨hi, ?_⟩
  rw [he]
  simp only [I_one]
  simp only [kanLaw]
  rw [I_sq_gauss _]
  rw [I_inv2 (show 4 < T - N + 1 by omega)]
  rw [I_inv (show 2 < T - N + 2 by omega)]
  rw [I_id_chi (N - 3)]
  ring

lemma m13 (hT : N + 7 < T) :
    Integrable (fun v : KanVar → ℝ => v .u0 * ((v .v2) ^ 2)⁻¹ * (v .w2)⁻¹ * f3 N (v .x21) ^ 2) (Measure.pi (kanLaw N T psi2)) ∧
    ∫ v, v .u0 * ((v .v2) ^ 2)⁻¹ * (v .w2)⁻¹ * f3 N (v .x21) ^ 2 ∂(Measure.pi (kanLaw N T psi2)) = (((N - 2 : ℕ) : ℝ)) * (1 / ((((T - N + 1 : ℕ) : ℝ) - 2) * (((T - N + 1 : ℕ) : ℝ) - 4))) * (1 / ((((T - N + 2 : ℕ) : ℝ)) - 2)) * (if 3 ≤ N then (1:ℝ) else 0) := by
  obtain ⟨hi, he⟩ := M12_spec (N := N) (T := T) (psi2 := psi2) one (fun x => x) (fun x => (x ^ 2)⁻¹) one (fun x => x⁻¹) one one one (fun x => f3 N x ^ 2) one one one
    (int_one _) (int_id_chi (N - 2)) (int_inv2_chi (show 4 < T - N + 1 by omega)) (int_one _) (int_inv_chi (show 2 < T - N + 2 by omega)) (int_one _) (int_one _) (int_one _) (int_f3sq N) (int_one _) (int_one _) (int_one _)
  have ef : (fun v : KanVar → ℝ => one (v .z2) * ((fun x => x)) (v .u0) * ((fun x => (x ^ 2)⁻¹)) (v .v2) * one (v .w1) * ((fun x => x⁻¹)) (v .w2) * one (v .s1) * one (v .s2) * one (v .x11) * ((fun x => f3 N x ^ 2)) (v .x21) * one (v .a) * one (v .b) * one (v .c)) = fun v => v .u0 * ((v .v2) ^ 2)⁻¹ * (v .w2)⁻¹ * f3 N (v .x21) ^ 2 := by
    funext v; simp only [one]; ring
  rw [ef] at hi he
  refine ⟨hi, ?_⟩
  rw [he]
  simp only [I_one]
  simp only [kanLaw]
  rw [I_id_chi (N - 2)]
  rw [I_inv2 (show 4 < T - N + 1 by omega)]
  rw [I_inv (show 2 < T - N + 2 by omega)]
  rw [I_f3sq N]
  ring

lemma m14 (hT : N + 7 < T) :
    Integrable (fun v : KanVar → ℝ => v .u0 * ((v .v2) ^ 2)⁻¹ * (v .w2)⁻¹ * v .s2) (Measure.pi (kanLaw N T psi2)) ∧
    ∫ v, v .u0 * ((v .v2) ^ 2)⁻¹ * (v .w2)⁻¹ * v .s2 ∂(Measure.pi (kanLaw N T psi2)) = (((N - 2 : ℕ) : ℝ)) * (1 / ((((T - N + 1 : ℕ) : ℝ) - 2) * (((T - N + 1 : ℕ) : ℝ) - 4))) * (1 / ((((T - N + 2 : ℕ) : ℝ)) - 2)) * (((N - 3 : ℕ) : ℝ)) := by
  obtain ⟨hi, he⟩ := M12_spec (N := N) (T := T) (psi2 := psi2) one (fun x => x) (fun x => (x ^ 2)⁻¹) one (fun x => x⁻¹) one (fun x => x) one one one one one
    (int_one _) (int_id_chi (N - 2)) (int_inv2_chi (show 4 < T - N + 1 by omega)) (int_one _) (int_inv_chi (show 2 < T - N + 2 by omega)) (int_one _) (int_id_chi (N - 3)) (int_one _) (int_one _) (int_one _) (int_one _) (int_one _)
  have ef : (fun v : KanVar → ℝ => one (v .z2) * ((fun x => x)) (v .u0) * ((fun x => (x ^ 2)⁻¹)) (v .v2) * one (v .w1) * ((fun x => x⁻¹)) (v .w2) * one (v .s1) * ((fun x => x)) (v .s2) * one (v .x11) * one (v .x21) * one (v .a) * one (v .b) * one (v .c)) = fun v => v .u0 * ((v .v2) ^ 2)⁻¹ * (v .w2)⁻¹ * v .s2 := by
    funext v; simp only [one]; ring
  rw [ef] at hi he
  refine ⟨hi, ?_⟩
  rw [he]
  simp only [I_one]
  simp only [kanLaw]
  rw [I_id_chi (N - 2)]
  rw [I_inv2 (show 4 < T - N + 1 by omega)]
  rw [I_inv (show 2 < T - N + 2 by omega)]
  rw [I_id_chi (N - 3)]
  ring

lemma m15 (hT : N + 7 < T) :
    Integrable (fun v : KanVar → ℝ => (v .w1)⁻¹ * (v .w2)⁻¹ * f3 N (v .x11) ^ 2 * f3 N (v .x21) ^ 2) (Measure.pi (kanLaw N T psi2)) := by
  obtain ⟨hi, he⟩ := M12_spec (N := N) (T := T) (psi2 := psi2) one one one (fun x => x⁻¹) (fun x => x⁻¹) one one (fun x => f3 N x ^ 2) (fun x => f3 N x ^ 2) one one one
    (int_one _) (int_one _) (int_one _) (int_inv_chi (show 2 < T - N + 3 by omega)) (int_inv_chi (show 2 < T - N + 2 by omega)) (int_one _) (int_one _) (int_f3sq N) (int_f3sq N) (int_one _) (int_one _) (int_one _)
  have ef : (fun v : KanVar → ℝ => one (v .z2) * one (v .u0) * one (v .v2) * ((fun x => x⁻¹)) (v .w1) * ((fun x => x⁻¹)) (v .w2) * one (v .s1) * one (v .s2) * ((fun x => f3 N x ^ 2)) (v .x11) * ((fun x => f3 N x ^ 2)) (v .x21) * one (v .a) * one (v .b) * one (v .c)) = fun v => (v .w1)⁻¹ * (v .w2)⁻¹ * f3 N (v .x11) ^ 2 * f3 N (v .x21) ^ 2 := by
    funext v; simp only [one]; ring
  rw [ef] at hi he
  exact hi

lemma m16 (hT : N + 7 < T) :
    Integrable (fun v : KanVar → ℝ => (v .w1)⁻¹ * ((v .w2) ^ 2)⁻¹ * f3 N (v .x21) ^ 4 * (v .b) ^ 2) (Measure.pi (kanLaw N T psi2)) := by
  obtain ⟨hi, he⟩ := M12_spec (N := N) (T := T) (psi2 := psi2) one one one (fun x => x⁻¹) (fun x => (x ^ 2)⁻¹) one one one (fun x => f3 N x ^ 4) one (fun x => x ^ 2) one
    (int_one _) (int_one _) (int_one _) (int_inv_chi (show 2 < T - N + 3 by omega)) (int_inv2_chi (show 4 < T - N + 2 by omega)) (int_one _) (int_one _) (int_one _) (int_f3_4 N) (int_one _) (int_sq_gauss 0) (int_one _)
  have ef : (fun v : KanVar → ℝ => one (v .z2) * one (v .u0) * one (v .v2) * ((fun x => x⁻¹)) (v .w1) * ((fun x => (x ^ 2)⁻¹)) (v .w2) * one (v .s1) * one (v .s2) * one (v .x11) * ((fun x => f3 N x ^ 4)) (v .x21) * one (v .a) * ((fun x => x ^ 2)) (v .b) * one (v .c)) = fun v => (v .w1)⁻¹ * ((v .w2) ^ 2)⁻¹ * f3 N (v .x21) ^ 4 * (v .b) ^ 2 := by
    funext v; simp only [one]; ring
  rw [ef] at hi he
  exact hi

lemma m17 (hT : N + 7 < T) :
    Integrable (fun v : KanVar → ℝ => (v .v2)⁻¹ * ((v .w2) ^ 2)⁻¹ * f3 N (v .x21) ^ 4 * (v .a) ^ 2) (Measure.pi (kanLaw N T psi2)) := by
  obtain ⟨hi, he⟩ := M12_spec (N := N) (T := T) (psi2 := psi2) one one (fun x => x⁻¹) one (fun x => (x ^ 2)⁻¹) one one one (fun x => f3 N x ^ 4) (fun x => x ^ 2) one one
    (int_one _) (int_one _) (int_inv_chi (show 2 < T - N + 1 by omega)) (int_one _) (int_inv2_chi (show 4 < T - N + 2 by omega)) (int_one _) (int_one _) (int_one _) (int_f3_4 N) (int_sq_gauss 0) (int_one _) (int_one _)
  have ef : (fun v : KanVar → ℝ => one (v .z2) * one (v .u0) * ((fun x => x⁻¹)) (v .v2) * one (v .w1) * ((fun x => (x ^ 2)⁻¹)) (v .w2) * one (v .s1) * one (v .s2) * one (v .x11) * ((fun x => f3 N x ^ 4)) (v .x21) * ((fun x => x ^ 2)) (v .a) * one (v .b) * one (v .c)) = fun v => (v .v2)⁻¹ * ((v .w2) ^ 2)⁻¹ * f3 N (v .x21) ^ 4 * (v .a) ^ 2 := by
    funext v; simp only [one]; ring
  rw [ef] at hi he
  exact hi

lemma m18 (hT : N + 7 < T) :
    Integrable (fun v : KanVar → ℝ => (v .w1)⁻¹ * (v .w2)⁻¹ * v .s2 * f4 N (v .c) ^ 2) (Measure.pi (kanLaw N T psi2)) := by
  obtain ⟨hi, he⟩ := M12_spec (N := N) (T := T) (psi2 := psi2) one one one (fun x => x⁻¹) (fun x => x⁻¹) one (fun x => x) one one one one (fun x => f4 N x ^ 2)
    (int_one _) (int_one _) (int_one _) (int_inv_chi (show 2 < T - N + 3 by omega)) (int_inv_chi (show 2 < T - N + 2 by omega)) (int_one _) (int_id_chi (N - 3)) (int_one _) (int_one _) (int_one _) (int_one _) (int_f4sq N)
  have ef : (fun v : KanVar → ℝ => one (v .z2) * one (v .u0) * one (v .v2) * ((fun x => x⁻¹)) (v .w1) * ((fun x => x⁻¹)) (v .w2) * one (v .s1) * ((fun x => x)) (v .s2) * one (v .x11) * one (v .x21) * one (v .a) * one (v .b) * ((fun x => f4 N x ^ 2)) (v .c)) = fun v => (v .w1)⁻¹ * (v .w2)⁻¹ * v .s2 * f4 N (v .c) ^ 2 := by
    funext v; simp only [one]; ring
  rw [ef] at hi he
  exact hi

lemma m19 (hT : N + 7 < T) :
    Integrable (fun v : KanVar → ℝ => (v .w1)⁻¹ * ((v .w2) ^ 2)⁻¹ * (v .s2) ^ 2 * (v .b) ^ 2) (Measure.pi (kanLaw N T psi2)) := by
  obtain ⟨hi, he⟩ := M12_spec (N := N) (T := T) (psi2 := psi2) one one one (fun x => x⁻¹) (fun x => (x ^ 2)⁻¹) one (fun x => x ^ 2) one one one (fun x => x ^ 2) one
    (int_one _) (int_one _) (int_one _) (int_inv_chi (show 2 < T - N + 3 by omega)) (int_inv2_chi (show 4 < T - N + 2 by omega)) (int_one _) (int_sq_chi (N - 3)) (int_one _) (int_one _) (int_one _) (int_sq_gauss 0) (int_one _)
  have ef : (fun v : KanVar → ℝ => one (v .z2) * one (v .u0) * one (v .v2) * ((fun x => x⁻¹)) (v .w1) * ((fun x => (x ^ 2)⁻¹)) (v .w2) * one (v .s1) * ((fun x => x ^ 2)) (v .s2) * one (v .x11) * one (v .x21) * one (v .a) * ((fun x => x ^ 2)) (v .b) * one (v .c)) = fun v => (v .w1)⁻¹ * ((v .w2) ^ 2)⁻¹ * (v .s2) ^ 2 * (v .b) ^ 2 := by
    funext v; simp only [one]; ring
  rw [ef] at hi he
  exact hi

lemma m20 (hT : N + 7 < T) :
    Integrable (fun v : KanVar → ℝ => (v .v2)⁻¹ * ((v .w2) ^ 2)⁻¹ * (v .s2) ^ 2 * (v .a) ^ 2) (Measure.pi (kanLaw N T psi2)) := by
  obtain ⟨hi, he⟩ := M12_spec (N := N) (T := T) (psi2 := psi2) one one (fun x => x⁻¹) one (fun x => (x ^ 2)⁻¹) one (fun x => x ^ 2) one one (fun x => x ^ 2) one one
    (int_one _) (int_one _) (int_inv_chi (show 2 < T - N + 1 by omega)) (int_one _) (int_inv2_chi (show 4 < T - N + 2 by omega)) (int_one _) (int_sq_chi (N - 3)) (int_one _) (int_one _) (int_sq_gauss 0) (int_one _) (int_one _)
  have ef : (fun v : KanVar → ℝ => one (v .z2) * one (v .u0) * ((fun x => x⁻¹)) (v .v2) * one (v .w1) * ((fun x => (x ^ 2)⁻¹)) (v .w2) * one (v .s1) * ((fun x => x ^ 2)) (v .s2) * one (v .x11) * one (v .x21) * ((fun x => x ^ 2)) (v .a) * one (v .b) * one (v .c)) = fun v => (v .v2)⁻¹ * ((v .w2) ^ 2)⁻¹ * (v .s2) ^ 2 * (v .a) ^ 2 := by
    funext v; simp only [one]; ring
  rw [ef] at hi he
  exact hi

end

end KanAux

namespace KanAux
open RiskEU.OOSUVar ChiTest

noncomputable def P1 (N : ℕ) (v : KanVar → ℝ) : ℝ := f3 N (v .x11) / √(v .w1)
noncomputable def P2 (N : ℕ) (v : KanVar → ℝ) : ℝ := v .b * f3 N (v .x21) / √(v .w1 * v .w2)
noncomputable def P3 (N : ℕ) (v : KanVar → ℝ) : ℝ := v .a * f3 N (v .x21) / √(v .v2 * v .w2)
noncomputable def Q1 (N : ℕ) (v : KanVar → ℝ) : ℝ := f4 N (v .c) / √(v .w1)
noncomputable def Q2 (v : KanVar → ℝ) : ℝ := v .b * √(v .s2) / √(v .w1 * v .w2)
noncomputable def Q3 (v : KanVar → ℝ) : ℝ := v .a * √(v .s2) / √(v .v2 * v .w2)

lemma y1_eq (N : ℕ) (v : KanVar → ℝ) : KanVar.y1 N v = P1 N v + P2 N v + P3 N v := rfl
lemma y2_eq (N : ℕ) (v : KanVar → ℝ) : KanVar.y2 N v = Q1 N v + Q2 v + Q3 v := rfl

lemma sq_div_sqrt (x w : ℝ) (hw : 0 ≤ w) : (x / √w) ^ 2 = x ^ 2 * w⁻¹ := by
  rw [div_pow, Real.sq_sqrt hw, div_eq_mul_inv]

/-- The `σ_g²` factor of (IA48). -/
noncomputable def Avar (N : ℕ) (v : KanVar → ℝ) : ℝ :=
  1 + KanVar.y1 N v ^ 2 + KanVar.y2 N v ^ 2 + v .s1 / v .w1 + v .a ^ 2 / v .v2
noncomputable def B2 (N : ℕ) (v : KanVar → ℝ) : ℝ :=
  (v .z2 ^ 2 + v .u0) * (v .v2 ^ 2)⁻¹ * (1 + (KanVar.x21' N v ^ 2 + v .s2) / v .w2)
noncomputable def Rr (v : KanVar → ℝ) : ℝ := √(v .z2 ^ 2 + v .u0) / v .v2
noncomputable def Cc (N : ℕ) (v : KanVar → ℝ) : ℝ :=
  v .a / √(v .v2) + KanVar.x21' N v * KanVar.y1 N v / √(v .w2) +
    √(v .s2) * KanVar.y2 N v / √(v .w2)

lemma kanVarRep_eq {N : ℕ} (M : Market N) (T : ℕ) (κ : ℝ) (v : KanVar → ℝ) :
    M.kanVarRep T κ v = M.sigmaG2 * Avar N v + (κ ^ 2 * T / M.gamma ^ 2) * B2 N v +
      (2 * κ * √T * √M.sigmaG2 / M.gamma) * (Rr v * Cc N v) := by
  unfold Market.kanVarRep Avar B2 Rr Cc
  ring

noncomputable def O1 (N : ℕ) (v : KanVar → ℝ) : ℝ :=
  P1 N v * P2 N v + P1 N v * P3 N v + Q1 N v * Q2 v + Q1 N v * Q3 v
noncomputable def O2 (N : ℕ) (v : KanVar → ℝ) : ℝ := P2 N v * P3 N v + Q2 v * Q3 v
noncomputable def Ae (N : ℕ) (v : KanVar → ℝ) : ℝ :=
  1 + P1 N v ^ 2 + P2 N v ^ 2 + P3 N v ^ 2 + Q1 N v ^ 2 + Q2 v ^ 2 + Q3 v ^ 2 +
    v .s1 / v .w1 + v .a ^ 2 / v .v2

lemma Avar_eq (N : ℕ) (v : KanVar → ℝ) : Avar N v = Ae N v + 2 * O1 N v + 2 * O2 N v := by
  unfold Avar Ae O1 O2; rw [y1_eq, y2_eq]; ring

lemma O1_odd (N : ℕ) (v : KanVar → ℝ) :
    O1 N (fun i => if i ∈ ({.x11, .c} : Finset KanVar) then -v i else v i) = - O1 N v := by
  unfold O1 P1 P2 P3 Q1 Q2 Q3
  simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, or_self, or_false, false_or,
    if_true, if_false, f3_neg, f4_neg]
  ring

lemma O2_odd (N : ℕ) (v : KanVar → ℝ) :
    O2 N (fun i => if i ∈ ({.a} : Finset KanVar) then -v i else v i) = - O2 N v := by
  unfold O2 P2 P3 Q2 Q3
  simp only [Finset.mem_singleton, reduceCtorEq, if_true, if_false]
  ring

lemma C3_odd (N : ℕ) (v : KanVar → ℝ) :
    Rr (fun i => if i ∈ ({.a, .b, .x11, .c} : Finset KanVar) then -v i else v i) *
      Cc N (fun i => if i ∈ ({.a, .b, .x11, .c} : Finset KanVar) then -v i else v i) =
      - (Rr v * Cc N v) := by
  unfold Rr Cc
  rw [y1_eq, y1_eq, y2_eq, y2_eq, x21'_eq, x21'_eq]
  unfold P1 P2 P3 Q1 Q2 Q3
  simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, or_self, or_false, false_or,
    if_true, if_false, f3_neg, f4_neg, or_true, true_or]
  ring

lemma measurable_P1 (N : ℕ) : Measurable (P1 N) := by
  have := measurable_f3 N; unfold P1; fun_prop
lemma measurable_P2 (N : ℕ) : Measurable (P2 N) := by
  have := measurable_f3 N; unfold P2; fun_prop
lemma measurable_P3 (N : ℕ) : Measurable (P3 N) := by
  have := measurable_f3 N; unfold P3; fun_prop
lemma measurable_Q1 (N : ℕ) : Measurable (Q1 N) := by
  have := measurable_f4 N; unfold Q1; fun_prop
lemma measurable_Q2 : Measurable Q2 := by unfold Q2; fun_prop
lemma measurable_Q3 : Measurable Q3 := by unfold Q3; fun_prop
lemma measurable_Rr : Measurable Rr := by unfold Rr; fun_prop
lemma measurable_Cc (N : ℕ) : Measurable (Cc N) := by
  have := measurable_y1 N; have := measurable_y2 N; have := measurable_x21' N
  unfold Cc; fun_prop
lemma measurable_O1 (N : ℕ) : Measurable (O1 N) := by
  have := measurable_P1 N; have := measurable_P2 N; have := measurable_P3 N
  have := measurable_Q1 N; have := measurable_Q2; have := measurable_Q3
  unfold O1; fun_prop
lemma measurable_O2 (N : ℕ) : Measurable (O2 N) := by
  have := measurable_P2 N; have := measurable_P3 N; have := measurable_Q2; have := measurable_Q3
  unfold O2; fun_prop

section
variable {N T : ℕ} {psi2 : ℝ}

lemma ae_pos_all : ∀ᵐ v ∂(Measure.pi (kanLaw N T psi2)),
    0 ≤ v .u0 ∧ 0 ≤ v .v2 ∧ 0 ≤ v .w1 ∧ 0 ≤ v .w2 ∧ 0 ≤ v .s1 ∧ 0 ≤ v .s2 := by
  filter_upwards [ae_nonneg_chi .u0 (N - 2) rfl, ae_nonneg_chi .v2 (T - N + 1) rfl,
    ae_nonneg_chi .w1 (T - N + 3) rfl, ae_nonneg_chi .w2 (T - N + 2) rfl,
    ae_nonneg_chi .s1 (N - 4) rfl, ae_nonneg_chi .s2 (N - 3) rfl] with v h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, h6⟩

variable (hT : N + 7 < T)
include hT

lemma P1_L2 : MemLp (P1 N) 2 (Measure.pi (kanLaw N T psi2)) :=
  memLp2_of_sq (measurable_P1 N).aestronglyMeasurable (m1 (psi2 := psi2) hT).1 (by
    filter_upwards [ae_pos_all] with v h
    unfold P1; rw [sq_div_sqrt _ _ h.2.2.1]; ring)
lemma P2_L2 : MemLp (P2 N) 2 (Measure.pi (kanLaw N T psi2)) :=
  memLp2_of_sq (measurable_P2 N).aestronglyMeasurable (m2 (psi2 := psi2) hT).1 (by
    filter_upwards [ae_pos_all] with v h
    unfold P2; rw [sq_div_sqrt _ _ (mul_nonneg h.2.2.1 h.2.2.2.1), mul_inv]; ring)
lemma P3_L2 : MemLp (P3 N) 2 (Measure.pi (kanLaw N T psi2)) :=
  memLp2_of_sq (measurable_P3 N).aestronglyMeasurable (m3 (psi2 := psi2) hT).1 (by
    filter_upwards [ae_pos_all] with v h
    unfold P3; rw [sq_div_sqrt _ _ (mul_nonneg h.2.1 h.2.2.2.1), mul_inv]; ring)
lemma Q1_L2 : MemLp (Q1 N) 2 (Measure.pi (kanLaw N T psi2)) :=
  memLp2_of_sq (measurable_Q1 N).aestronglyMeasurable (m4 (psi2 := psi2) hT).1 (by
    filter_upwards [ae_pos_all] with v h
    unfold Q1; rw [sq_div_sqrt _ _ h.2.2.1]; ring)
lemma Q2_L2 : MemLp Q2 2 (Measure.pi (kanLaw N T psi2)) :=
  memLp2_of_sq measurable_Q2.aestronglyMeasurable (m5 (psi2 := psi2) hT).1 (by
    filter_upwards [ae_pos_all] with v h
    unfold Q2; rw [sq_div_sqrt _ _ (mul_nonneg h.2.2.1 h.2.2.2.1), mul_inv, mul_pow,
      Real.sq_sqrt h.2.2.2.2.2]; ring)
lemma Q3_L2 : MemLp Q3 2 (Measure.pi (kanLaw N T psi2)) :=
  memLp2_of_sq measurable_Q3.aestronglyMeasurable (m6 (psi2 := psi2) hT).1 (by
    filter_upwards [ae_pos_all] with v h
    unfold Q3; rw [sq_div_sqrt _ _ (mul_nonneg h.2.1 h.2.2.2.1), mul_inv, mul_pow,
      Real.sq_sqrt h.2.2.2.2.2]; ring)

lemma Rr_L2 : MemLp Rr 2 (Measure.pi (kanLaw N T psi2)) :=
  memLp2_of_sq measurable_Rr.aestronglyMeasurable
    ((m9 (psi2 := psi2) hT).1.add (m10 (psi2 := psi2) hT).1) (by
    filter_upwards [ae_pos_all] with v h
    unfold Rr; simp only [Pi.add_apply]
    rw [div_pow, Real.sq_sqrt (by nlinarith [sq_nonneg (v .z2)]), div_eq_mul_inv]; ring)

lemma Cc_L2 : MemLp (Cc N) 2 (Measure.pi (kanLaw N T psi2)) := by
  have hm := measurable_f3 N
  have hm4 := measurable_f4 N
  have a0 : MemLp (fun v : KanVar → ℝ => v .a / √(v .v2)) 2 (Measure.pi (kanLaw N T psi2)) :=
    memLp2_of_sq (Measurable.aestronglyMeasurable (by fun_prop)) (m8 (psi2 := psi2) hT).1 (by
      filter_upwards [ae_pos_all] with v h
      rw [sq_div_sqrt _ _ h.2.1]; ring)
  have a1 : MemLp (fun v => f3 N (v .x21) * P1 N v / √(v .w2)) 2 (Measure.pi (kanLaw N T psi2)) :=
    memLp2_of_sq (Measurable.aestronglyMeasurable (by have := measurable_P1 N; fun_prop)) (m15 (psi2 := psi2) hT) (by
      filter_upwards [ae_pos_all] with v h
      unfold P1; rw [sq_div_sqrt _ _ h.2.2.2.1, mul_pow, sq_div_sqrt _ _ h.2.2.1]; ring)
  have a2 : MemLp (fun v => f3 N (v .x21) * P2 N v / √(v .w2)) 2 (Measure.pi (kanLaw N T psi2)) :=
    memLp2_of_sq (Measurable.aestronglyMeasurable (by have := measurable_P2 N; fun_prop)) (m16 (psi2 := psi2) hT) (by
      filter_upwards [ae_pos_all] with v h
      unfold P2; rw [sq_div_sqrt _ _ h.2.2.2.1, mul_pow,
        sq_div_sqrt _ _ (mul_nonneg h.2.2.1 h.2.2.2.1), mul_inv]; ring)
  have a3 : MemLp (fun v => f3 N (v .x21) * P3 N v / √(v .w2)) 2 (Measure.pi (kanLaw N T psi2)) :=
    memLp2_of_sq (Measurable.aestronglyMeasurable (by have := measurable_P3 N; fun_prop)) (m17 (psi2 := psi2) hT) (by
      filter_upwards [ae_pos_all] with v h
      unfold P3; rw [sq_div_sqrt _ _ h.2.2.2.1, mul_pow,
        sq_div_sqrt _ _ (mul_nonneg h.2.1 h.2.2.2.1), mul_inv]; ring)
  have b1 : MemLp (fun v => √(v .s2) * Q1 N v / √(v .w2)) 2 (Measure.pi (kanLaw N T psi2)) :=
    memLp2_of_sq (Measurable.aestronglyMeasurable (by have := measurable_Q1 N; fun_prop)) (m18 (psi2 := psi2) hT) (by
      filter_upwards [ae_pos_all] with v h
      unfold Q1; rw [sq_div_sqrt _ _ h.2.2.2.1, mul_pow, sq_div_sqrt _ _ h.2.2.1,
        Real.sq_sqrt h.2.2.2.2.2]; ring)
  have b2 : MemLp (fun v => √(v .s2) * Q2 v / √(v .w2)) 2 (Measure.pi (kanLaw N T psi2)) :=
    memLp2_of_sq (Measurable.aestronglyMeasurable (by have := measurable_Q2; fun_prop)) (m19 (psi2 := psi2) hT) (by
      filter_upwards [ae_pos_all] with v h
      unfold Q2; rw [sq_div_sqrt _ _ h.2.2.2.1, mul_pow,
        sq_div_sqrt _ _ (mul_nonneg h.2.2.1 h.2.2.2.1), mul_inv, mul_pow,
        Real.sq_sqrt h.2.2.2.2.2]; ring)
  have b3 : MemLp (fun v => √(v .s2) * Q3 v / √(v .w2)) 2 (Measure.pi (kanLaw N T psi2)) :=
    memLp2_of_sq (Measurable.aestronglyMeasurable (by have := measurable_Q3; fun_prop)) (m20 (psi2 := psi2) hT) (by
      filter_upwards [ae_pos_all] with v h
      unfold Q3; rw [sq_div_sqrt _ _ h.2.2.2.1, mul_pow,
        sq_div_sqrt _ _ (mul_nonneg h.2.1 h.2.2.2.1), mul_inv, mul_pow,
        Real.sq_sqrt h.2.2.2.2.2]; ring)
  have hs := ((((((a0.add a1).add a2).add a3).add b1).add b2).add b3)
  refine hs.congr_norm (measurable_Cc N).aestronglyMeasurable (ae_of_all _ fun v => ?_)
  congr 1
  simp only [Pi.add_apply, Cc]
  rw [y1_eq, y2_eq, x21'_eq]
  ring

end

end KanAux

namespace KanAux
open RiskEU.OOSUVar ChiTest

section
variable {N T : ℕ} {psi2 : ℝ}

lemma P1_sq : ∀ᵐ v ∂(Measure.pi (kanLaw N T psi2)), P1 N v ^ 2 = (v .w1)⁻¹ * f3 N (v .x11) ^ 2 := by
  filter_upwards [ae_pos_all] with v h
  unfold P1; rw [sq_div_sqrt _ _ h.2.2.1]; ring
lemma P2_sq : ∀ᵐ v ∂(Measure.pi (kanLaw N T psi2)),
    P2 N v ^ 2 = (v .w1)⁻¹ * (v .w2)⁻¹ * f3 N (v .x21) ^ 2 * (v .b) ^ 2 := by
  filter_upwards [ae_pos_all] with v h
  unfold P2; rw [sq_div_sqrt _ _ (mul_nonneg h.2.2.1 h.2.2.2.1), mul_inv]; ring
lemma P3_sq : ∀ᵐ v ∂(Measure.pi (kanLaw N T psi2)),
    P3 N v ^ 2 = (v .v2)⁻¹ * (v .w2)⁻¹ * f3 N (v .x21) ^ 2 * (v .a) ^ 2 := by
  filter_upwards [ae_pos_all] with v h
  unfold P3; rw [sq_div_sqrt _ _ (mul_nonneg h.2.1 h.2.2.2.1), mul_inv]; ring
lemma Q1_sq : ∀ᵐ v ∂(Measure.pi (kanLaw N T psi2)), Q1 N v ^ 2 = (v .w1)⁻¹ * f4 N (v .c) ^ 2 := by
  filter_upwards [ae_pos_all] with v h
  unfold Q1; rw [sq_div_sqrt _ _ h.2.2.1]; ring
lemma Q2_sq : ∀ᵐ v ∂(Measure.pi (kanLaw N T psi2)),
    Q2 v ^ 2 = (v .w1)⁻¹ * (v .w2)⁻¹ * v .s2 * (v .b) ^ 2 := by
  filter_upwards [ae_pos_all] with v h
  unfold Q2; rw [sq_div_sqrt _ _ (mul_nonneg h.2.2.1 h.2.2.2.1), mul_inv, mul_pow,
    Real.sq_sqrt h.2.2.2.2.2]; ring
lemma Q3_sq : ∀ᵐ v ∂(Measure.pi (kanLaw N T psi2)),
    Q3 v ^ 2 = (v .v2)⁻¹ * (v .w2)⁻¹ * v .s2 * (v .a) ^ 2 := by
  filter_upwards [ae_pos_all] with v h
  unfold Q3; rw [sq_div_sqrt _ _ (mul_nonneg h.2.1 h.2.2.2.1), mul_inv, mul_pow,
    Real.sq_sqrt h.2.2.2.2.2]; ring

end

end KanAux


namespace KanAux
open RiskEU.OOSUVar ChiTest

lemma int_f4_4 (N : ℕ) : Integrable (fun x => f4 N x ^ 4) (gaussianReal 0 1) := by
  unfold f4; split_ifs
  · exact gauss_int_pow 4
  · simp
lemma I_f3_4 (N : ℕ) : ∫ x, f3 N x ^ 4 ∂(gaussianReal 0 1) = if 3 ≤ N then 3 else 0 := by
  unfold f3; split_ifs
  · exact gauss_moment4
  · simp
lemma I_f4_4 (N : ℕ) : ∫ x, f4 N x ^ 4 ∂(gaussianReal 0 1) = if 4 ≤ N then 3 else 0 := by
  unfold f4; split_ifs
  · exact gauss_moment4
  · simp
lemma I_x4 : ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 := gauss_moment4
lemma I_sq_chi (k : ℕ) : ∫ x, x ^ 2 ∂(chiSq k) = k * (k + 2) := (chiSq_moment2 k).2

/-- Transfer from an arbitrary Kan family to the canonical product space. -/
lemma fam_transfer {N T : ℕ} {psi2 : ℝ} {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    {X : KanVar → Ω' → ℝ} (hX : IsKanFamily N T psi2 Q X) (F : (KanVar → ℝ) → ℝ)
    (hF : Measurable F) :
    (Integrable (fun ω => F (fun i => X i ω)) Q ↔ Integrable F (Measure.pi (kanLaw N T psi2))) ∧
    ∫ ω, F (fun i => X i ω) ∂Q = ∫ v, F v ∂(Measure.pi (kanLaw N T psi2)) := by
  have h := hX.1.hasLaw_pi hX.2
  constructor
  · rw [← h.map_eq, integrable_map_measure hF.aestronglyMeasurable h.aemeasurable]
    rfl
  · rw [← h.map_eq, integral_map h.aemeasurable hF.aestronglyMeasurable]

lemma inv_sqrt_sq (w : ℝ) (hw : 0 ≤ w) : ((√w)⁻¹) ^ 2 = w⁻¹ := by
  rw [inv_pow, Real.sq_sqrt hw]

lemma memLp2_of_sq' {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f G : Ω → ℝ}
    (hf : Measurable f) (hG : Integrable G μ) (h : ∀ᵐ x ∂μ, f x ^ 2 = G x) :
    MemLp f 2 μ := memLp2_of_sq hf.aestronglyMeasurable hG h

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

lemma sigmaG2_nonneg {N : ℕ} (M : Market N) (hS : M.Sigma.PosDef) : 0 ≤ M.sigmaG2 := by
  have hSi : (M.Sigma⁻¹).PosSemidef := hS.posSemidef.inv
  have := hSi.dotProduct_mulVec_nonneg (ones N)
  unfold Market.sigmaG2
  apply inv_nonneg.2
  simpa using this

end KanAux

namespace KanAux
open RiskEU.OOSUVar ChiTest

/-! ### Independence of functions of disjoint coordinate blocks -/

section Split
variable {N T : ℕ} {psi2 : ℝ}

/-- The block `{z₂, u₀}` of the Kan coordinates. -/
def blkS : Finset KanVar := {.z2, .u0}
/-- The complementary block. -/
def blkT : Finset KanVar := {.v2, .w1, .w2, .s1, .s2, .x11, .x21, .a, .b, .c}

noncomputable def extS (w : blkS → ℝ) : KanVar → ℝ := fun i => if h : i ∈ blkS then w ⟨i, h⟩ else 0
noncomputable def extT (w : blkT → ℝ) : KanVar → ℝ := fun i => if h : i ∈ blkT then w ⟨i, h⟩ else 0

lemma measurable_extS : Measurable extS := by
  refine measurable_pi_iff.2 fun i => ?_
  unfold extS
  by_cases h : i ∈ blkS
  · simp only [h, dif_pos]; exact measurable_pi_apply _
  · simp only [h, dif_neg, not_false_eq_true]; exact measurable_const

lemma measurable_extT : Measurable extT := by
  refine measurable_pi_iff.2 fun i => ?_
  unfold extT
  by_cases h : i ∈ blkT
  · simp only [h, dif_pos]; exact measurable_pi_apply _
  · simp only [h, dif_neg, not_false_eq_true]; exact measurable_const

/-- If `f` depends only on `(z₂, u₀)` and `g` only on the other coordinates, then
`E[f g] = E[f] E[g]` under the product law. -/
lemma integral_mul_split (f g : (KanVar → ℝ) → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfS : ∀ v, f (extS (fun i : blkS => v i)) = f v)
    (hgT : ∀ v, g (extT (fun i : blkT => v i)) = g v) :
    ∫ v, f v * g v ∂(Measure.pi (kanLaw N T psi2)) =
      (∫ v, f v ∂(Measure.pi (kanLaw N T psi2))) * ∫ v, g v ∂(Measure.pi (kanLaw N T psi2)) := by
  have hind := (canonical_isKan N T psi2).1
  have hdis : Disjoint blkS blkT := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [blkS, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> simp [blkT] at hb
  have h := hind.indepFun_finset blkS blkT hdis (fun i => measurable_pi_apply i)
  have h2 := h.comp (hf.comp measurable_extS) (hg.comp measurable_extT)
  have ef : (f ∘ extS) ∘ (fun v (i : blkS) => v i) = f := by
    funext v; exact hfS v
  have eg : (g ∘ extT) ∘ (fun v (i : blkT) => v i) = g := by
    funext v; exact hgT v
  rw [ef, eg] at h2
  exact h2.integral_fun_mul_eq_mul_integral hf.aestronglyMeasurable hg.aestronglyMeasurable

lemma indep_split (f g : (KanVar → ℝ) → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfS : ∀ v, f (extS (fun i : blkS => v i)) = f v)
    (hgT : ∀ v, g (extT (fun i : blkT => v i)) = g v) :
    IndepFun f g (Measure.pi (kanLaw N T psi2)) := by
  have hind := (canonical_isKan N T psi2).1
  have hdis : Disjoint blkS blkT := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [blkS, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> simp [blkT] at hb
  have h := hind.indepFun_finset blkS blkT hdis (fun i => measurable_pi_apply i)
  have h2 := h.comp (hf.comp measurable_extS) (hg.comp measurable_extT)
  have ef : (f ∘ extS) ∘ (fun v (i : blkS) => v i) = f := by
    funext v; exact hfS v
  have eg : (g ∘ extT) ∘ (fun v (i : blkT) => v i) = g := by
    funext v; exact hgT v
  rw [ef, eg] at h2
  exact h2

end Split

end KanAux

namespace KanAux
open RiskEU.OOSUVar ChiTest

lemma measurable_Avar (N : ℕ) : Measurable (Avar N) := by
  have := measurable_y1 N; have := measurable_y2 N
  unfold Avar; fun_prop

lemma measurable_B2 {N : ℕ} : Measurable (B2 N) := by
  have := measurable_x21' N; unfold B2; fun_prop

lemma Avar_flip4 (N : ℕ) (v : KanVar → ℝ) :
    Avar N (fun i => if i ∈ ({.a, .b, .x11, .c} : Finset KanVar) then -v i else v i) = Avar N v := by
  unfold Avar
  rw [y1_eq, y1_eq, y2_eq, y2_eq]
  unfold P1 P2 P3 Q1 Q2 Q3
  simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, or_self, or_false, false_or,
    if_true, if_false, f3_neg, f4_neg, or_true, true_or]
  ring

lemma B2_flip (N : ℕ) (S : Finset KanVar) (hS : S ⊆ {.a, .b, .x11, .c}) (v : KanVar → ℝ) :
    B2 N (fun i => if i ∈ S then -v i else v i) = B2 N v := by
  have h1 : KanVar.z2 ∉ S := fun h => by simpa using hS h
  have h2 : KanVar.u0 ∉ S := fun h => by simpa using hS h
  have h3 : KanVar.v2 ∉ S := fun h => by simpa using hS h
  have h4 : KanVar.w2 ∉ S := fun h => by simpa using hS h
  have h5 : KanVar.s2 ∉ S := fun h => by simpa using hS h
  have h6 : KanVar.x21 ∉ S := fun h => by simpa using hS h
  unfold B2 KanVar.x21'
  simp only [h1, h2, h3, h4, h5, h6, if_false]

/-! ### The building blocks of (IA50) -/

noncomputable def Sz (v : KanVar → ℝ) : ℝ := v .z2 ^ 2 + v .u0
noncomputable def Bp (N : ℕ) (v : KanVar → ℝ) : ℝ :=
  1 / v .v2 ^ 2 * (1 + (KanVar.x21' N v ^ 2 + v .s2) / v .w2)
noncomputable def Cq (N : ℕ) (v : KanVar → ℝ) : ℝ := 1 / v .v2 ^ 2 * Cc N v ^ 2
noncomputable def I55 (N : ℕ) (v : KanVar → ℝ) : ℝ := 1 / v .v2 ^ 2 * Avar N v
noncomputable def I56 (N : ℕ) (v : KanVar → ℝ) : ℝ :=
  1 / (v .v2 ^ 2 * v .w2) * (KanVar.x21' N v ^ 2 + v .s2) * Avar N v

lemma measurable_Sz : Measurable Sz := by unfold Sz; fun_prop
lemma measurable_Bp (N : ℕ) : Measurable (Bp N) := by
  have := measurable_x21' N; unfold Bp; fun_prop
lemma measurable_Cq (N : ℕ) : Measurable (Cq N) := by
  have := measurable_Cc N; unfold Cq; fun_prop
lemma measurable_I55 (N : ℕ) : Measurable (I55 N) := by
  have := measurable_Avar N; unfold I55; fun_prop
lemma measurable_I56 (N : ℕ) : Measurable (I56 N) := by
  have := measurable_Avar N; have := measurable_x21' N; unfold I56; fun_prop

lemma B2_eq_SzBp (N : ℕ) (v : KanVar → ℝ) : B2 N v = Sz v * Bp N v := by
  unfold B2 Sz Bp; ring

lemma BpA_eq (N : ℕ) (v : KanVar → ℝ) : Bp N v * Avar N v = I55 N v + I56 N v := by
  unfold Bp I55 I56; ring

lemma Sz_S (v : KanVar → ℝ) : Sz (extS (fun i : blkS => v i)) = Sz v := by
  simp [Sz, extS, blkS]
lemma Sz2_S (v : KanVar → ℝ) :
    (fun v => Sz v ^ 2) (extS (fun i : blkS => v i)) = Sz v ^ 2 := by
  simp only [Sz_S]
lemma Bp_T (N : ℕ) (v : KanVar → ℝ) : Bp N (extT (fun i : blkT => v i)) = Bp N v := by
  simp [Bp, extT, blkT, KanVar.x21']
lemma Bp2_T (N : ℕ) (v : KanVar → ℝ) :
    (fun v => Bp N v ^ 2) (extT (fun i : blkT => v i)) = Bp N v ^ 2 := by
  simp only [Bp_T]
lemma Cq_T (N : ℕ) (v : KanVar → ℝ) : Cq N (extT (fun i : blkT => v i)) = Cq N v := by
  simp [Cq, Cc, extT, blkT, KanVar.x21', KanVar.x11', KanVar.c', KanVar.y1, KanVar.y2]
lemma I55_T (N : ℕ) (v : KanVar → ℝ) : I55 N (extT (fun i : blkT => v i)) = I55 N v := by
  simp [I55, Avar, extT, blkT, KanVar.x21', KanVar.x11', KanVar.c', KanVar.y1, KanVar.y2]
lemma I56_T (N : ℕ) (v : KanVar → ℝ) : I56 N (extT (fun i : blkT => v i)) = I56 N v := by
  simp [I56, Avar, extT, blkT, KanVar.x21', KanVar.x11', KanVar.c', KanVar.y1, KanVar.y2]
lemma BpA_T (N : ℕ) (v : KanVar → ℝ) :
    (fun v => Bp N v * Avar N v) (extT (fun i : blkT => v i)) = Bp N v * Avar N v := by
  simp only [BpA_eq, I55_T, I56_T]

end KanAux

open RiskEU.OOSUVar KanAux ChiTest in
set_option maxHeartbeats 2000000 in
theorem solution {N T : ℕ} (M : Market N) (hM : M.Standing T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin T → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r)
    (κ : ℝ) (hκ : κ ∈ Set.Icc (0 : ℝ) 1) :
    MemLp (fun ω => M.oosVar κ (sampleData r ω)) 2 P ∧
    variance (fun ω => M.oosVar κ (sampleData r ω)) P =
      2 * M.sigmaG2 ^ 2 * (((N : ℝ) - 1) * ((T : ℝ) - 2) /
          (((T : ℝ) - N - 1) ^ 2 * ((T : ℝ) - N - 3))) +
        4 * κ ^ 2 * M.sigmaG2 / M.gamma ^ 2 *
          ((T : ℝ) * ((T : ℝ) - 2) * ((T : ℝ) + N - 3) * ((T : ℝ) * M.psi2 + N - 1) /
            (((T : ℝ) - N) * ((T : ℝ) - N - 1) ^ 2 * ((T : ℝ) - N - 3) * ((T : ℝ) - N - 5))) +
        2 * κ ^ 4 / M.gamma ^ 4 *
          ((T : ℝ) ^ 2 * ((T : ℝ) - 2) * C T N M.psi2 /
            (((T : ℝ) - N) ^ 2 * ((T : ℝ) - N - 1) ^ 2 * ((T : ℝ) - N - 2) * ((T : ℝ) - N - 3) ^ 2 *
              ((T : ℝ) - N - 5) * ((T : ℝ) - N - 7))) := by
  have hT : N + 7 < T := hM.2.1
  have hN2 : 2 ≤ N := hM.1
  have hψ : 0 ≤ M.psi2 := psi2_nonneg M hM.2.2.1
  have hσ : 0 ≤ M.sigmaG2 := sigmaG2_nonneg M hM.2.2.1
  have hγ : M.gamma ≠ 0 := hM.2.2.2.ne'
  -- (IA49) for the first moment
  obtain ⟨hI49, hE49⟩ := eq_IA49 M hM P r hr κ hκ
  -- transfer of the second moment through the Kan et al. representation
  obtain ⟨hI2, hE2⟩ := kan_transfer M hM P r hr κ hκ (fun p => p.2 ^ 2) (measurable_snd.pow_const 2)
  simp only at hI2 hE2
  set μK := Measure.pi (kanLaw N T M.psi2) with hμK
  have hXc := canonical_isKan N T M.psi2
  -- the auxiliary expectations (IA51)–(IA57), on the canonical space
  have c51 : Integrable Sz μK ∧ ∫ v, Sz v ∂μK = (N : ℝ) - 1 + T * M.psi2 :=
    eq_IA51 hN2 hT M.psi2 hψ μK (fun i v => v i) hXc
  have c52 : Integrable (fun v => Sz v ^ 2) μK ∧ ∫ v, Sz v ^ 2 ∂μK =
      ((N : ℝ) + 1) * ((N : ℝ) - 1) + 2 * T * ((N : ℝ) + 1) * M.psi2 + (T : ℝ) ^ 2 * M.psi2 ^ 2 :=
    eq_IA52 hN2 hT M.psi2 hψ μK (fun i v => v i) hXc
  have c53 : Integrable (fun v => Avar N v ^ 2) μK ∧ ∫ v, Avar N v ^ 2 ∂μK =
      ((T : ℝ) - 2) * ((T : ℝ) - 4) / (((T : ℝ) - N - 1) * ((T : ℝ) - N - 3)) :=
    eq_IA53 hN2 hT M.psi2 hψ μK (fun i v => v i) hXc
  have c54 : Integrable (Cq N) μK ∧ ∫ v, Cq N v ∂μK =
      ((T : ℝ) - 2) * ((T : ℝ) + N - 3) /
        (((T : ℝ) - N + 1) * ((T : ℝ) - N) * ((T : ℝ) - N - 1) * ((T : ℝ) - N - 3) * ((T : ℝ) - N - 5)) :=
    eq_IA54 hN2 hT M.psi2 hψ μK (fun i v => v i) hXc
  have c55 : Integrable (I55 N) μK ∧ ∫ v, I55 N v ∂μK =
      ((T : ℝ) - 2) * ((T : ℝ) - N - 4) /
        (((T : ℝ) - N) * ((T : ℝ) - N - 1) * ((T : ℝ) - N - 3) * ((T : ℝ) - N - 5)) :=
    eq_IA55 hN2 hT M.psi2 hψ μK (fun i v => v i) hXc
  have c56 : Integrable (I56 N) μK ∧ ∫ v, I56 N v ∂μK =
      ((T : ℝ) - 2) * ((N : ℝ) - 2) /
        (((T : ℝ) - N + 1) * ((T : ℝ) - N) * ((T : ℝ) - N - 1) * ((T : ℝ) - N - 5)) :=
    eq_IA56 hN2 hT M.psi2 hψ μK (fun i v => v i) hXc
  have c57' := eq_IA57 hN2 hT M.psi2 hψ μK (fun i v => v i) hXc
  have hBp2 : ∀ v : KanVar → ℝ, Bp N v ^ 2 = 1 / v .v2 ^ 4 *
      (1 + (KanVar.x21' N v ^ 2 + v .s2) / v .w2) ^ 2 := fun v => by unfold Bp; ring
  have c57 : Integrable (fun v => Bp N v ^ 2) μK ∧ ∫ v, Bp N v ^ 2 ∂μK =
      ((T : ℝ) - 2) * ((T : ℝ) - 4) /
        (((T : ℝ) - N) * ((T : ℝ) - N - 1) * ((T : ℝ) - N - 2) * ((T : ℝ) - N - 3) *
          ((T : ℝ) - N - 5) * ((T : ℝ) - N - 7)) := by
    simp_rw [hBp2]; exact c57'
  -- independence of the (z₂, u₀) block from the rest
  have iSB : IndepFun (fun v => Sz v ^ 2) (fun v => Bp N v ^ 2) μK :=
    indep_split _ _ (measurable_Sz.pow_const 2) ((measurable_Bp N).pow_const 2) Sz2_S (Bp2_T N)
  have iSC : IndepFun Sz (Cq N) μK :=
    indep_split _ _ measurable_Sz (measurable_Cq N) Sz_S (Cq_T N)
  have mBA : Measurable (fun v => Bp N v * Avar N v) := (measurable_Bp N).mul (measurable_Avar N)
  have iSA : IndepFun Sz (fun v => Bp N v * Avar N v) μK :=
    indep_split _ _ measurable_Sz mBA Sz_S (BpA_T N)
  have eSB : ∫ v, Sz v ^ 2 * Bp N v ^ 2 ∂μK = (∫ v, Sz v ^ 2 ∂μK) * ∫ v, Bp N v ^ 2 ∂μK :=
    integral_mul_split _ _ (measurable_Sz.pow_const 2) ((measurable_Bp N).pow_const 2) Sz2_S (Bp2_T N)
  have eSC : ∫ v, Sz v * Cq N v ∂μK = (∫ v, Sz v ∂μK) * ∫ v, Cq N v ∂μK :=
    integral_mul_split _ _ measurable_Sz (measurable_Cq N) Sz_S (Cq_T N)
  have eSA : ∫ v, Sz v * (Bp N v * Avar N v) ∂μK =
      (∫ v, Sz v ∂μK) * ∫ v, Bp N v * Avar N v ∂μK :=
    integral_mul_split _ _ measurable_Sz mBA Sz_S (BpA_T N)
  have iBA : Integrable (fun v => Bp N v * Avar N v) μK :=
    (c55.1.add c56.1).congr (ae_of_all _ fun v => by simp only [Pi.add_apply]; rw [BpA_eq])
  have eBA : ∫ v, Bp N v * Avar N v ∂μK = (∫ v, I55 N v ∂μK) + ∫ v, I56 N v ∂μK := by
    rw [← integral_add c55.1 c56.1]; exact integral_congr_ae (ae_of_all _ fun v => BpA_eq N v)
  -- square integrability of the three components of (IA48)
  have aA : MemLp (Avar N) 2 μK :=
    (memLp_two_iff_integrable_sq (measurable_Avar N).aestronglyMeasurable).2 c53.1
  have iB2 : Integrable (fun v => B2 N v ^ 2) μK :=
    (iSB.integrable_mul c52.1 c57.1).congr (ae_of_all _ fun v => by
      simp only [Pi.mul_apply]; rw [B2_eq_SzBp]; ring)
  have aB : MemLp (B2 N) 2 μK :=
    (memLp_two_iff_integrable_sq measurable_B2.aestronglyMeasurable).2 iB2
  have mRC : Measurable (fun v => Rr v * Cc N v) := measurable_Rr.mul (measurable_Cc N)
  have hRC2 : ∀ᵐ v ∂μK, (Rr v * Cc N v) ^ 2 = Sz v * Cq N v := by
    filter_upwards [ae_pos_all] with v h
    unfold Rr Sz Cq
    rw [mul_pow, div_pow, Real.sq_sqrt (by nlinarith [sq_nonneg (v .z2), h.1])]
    ring
  have iRC2 : Integrable (fun v => (Rr v * Cc N v) ^ 2) μK :=
    (iSC.integrable_mul c51.1 c54.1).congr (hRC2.mono fun v h => by simp only [Pi.mul_apply]; rw [h])
  have aRC : MemLp (fun v => Rr v * Cc N v) 2 μK :=
    (memLp_two_iff_integrable_sq mRC.aestronglyMeasurable).2 iRC2
  -- the representation and its second moment
  set σ2 := M.sigmaG2
  set K := κ ^ 2 * T / M.gamma ^ 2
  set L := 2 * κ * √T * √M.sigmaG2 / M.gamma
  have hrep := funext (kanVarRep_eq M T κ)
  have aW : MemLp (fun v => σ2 * Avar N v + K * B2 N v) 2 μK := (aA.const_mul _).add (aB.const_mul _)
  have aV : MemLp (fun v => M.kanVarRep T κ v) 2 μK := by
    rw [hrep]; exact aW.add (aRC.const_mul _)
  have hS4 : ∀ i ∈ ({.a, .b, .x11, .c} : Finset KanVar), kanLaw N T M.psi2 i = gaussianReal 0 1 := by
    intro i hi; simp at hi; rcases hi with rfl | rfl | rfl | rfl <;> rfl
  have zX : ∫ v, (σ2 * Avar N v + K * B2 N v) * (Rr v * Cc N v) ∂μK = 0 :=
    odd_integral_zero _ hS4 _ ((((measurable_Avar N).const_mul _).add (measurable_B2.const_mul _)).mul mRC)
      (fun v => by
        rw [Avar_flip4, B2_flip N _ (by intro i; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto), C3_odd]
        ring)
  have iW2 := aW.integrable_sq
  have iWRC := aW.integrable_mul aRC
  have sq_exp : (fun v => M.kanVarRep T κ v ^ 2) = fun v =>
      (σ2 * Avar N v + K * B2 N v) ^ 2 + 2 * L * ((σ2 * Avar N v + K * B2 N v) * (Rr v * Cc N v)) +
        L ^ 2 * (Rr v * Cc N v) ^ 2 := by
    funext v; rw [kanVarRep_eq]; ring
  have iA2 := c53.1
  have iAB' := aA.integrable_mul aB
  have w_exp : (fun v => (σ2 * Avar N v + K * B2 N v) ^ 2) = fun v =>
      σ2 ^ 2 * Avar N v ^ 2 + 2 * σ2 * K * (Avar N v * B2 N v) + K ^ 2 * B2 N v ^ 2 := by
    funext v; ring
  have eAB : ∫ v, Avar N v * B2 N v ∂μK = ∫ v, Sz v * (Bp N v * Avar N v) ∂μK :=
    integral_congr_ae (ae_of_all _ fun v => by simp only; rw [B2_eq_SzBp]; ring)
  have eB2 : ∫ v, B2 N v ^ 2 ∂μK = ∫ v, Sz v ^ 2 * Bp N v ^ 2 ∂μK :=
    integral_congr_ae (ae_of_all _ fun v => by simp only; rw [B2_eq_SzBp]; ring)
  have eRC2 : ∫ v, (Rr v * Cc N v) ^ 2 ∂μK = ∫ v, Sz v * Cq N v ∂μK := integral_congr_ae hRC2
  have EW2 : ∫ v, (σ2 * Avar N v + K * B2 N v) ^ 2 ∂μK =
      σ2 ^ 2 * (∫ v, Avar N v ^ 2 ∂μK) + 2 * σ2 * K * (∫ v, Avar N v * B2 N v ∂μK) +
        K ^ 2 * (∫ v, B2 N v ^ 2 ∂μK) := by
    rw [w_exp, integral_add (f := fun v => σ2 ^ 2 * Avar N v ^ 2 + 2 * σ2 * K * (Avar N v * B2 N v))
      (g := fun v => K ^ 2 * B2 N v ^ 2) ((iA2.const_mul _).add (iAB'.const_mul _)) (iB2.const_mul _),
      integral_add (f := fun v => σ2 ^ 2 * Avar N v ^ 2) (g := fun v => 2 * σ2 * K * (Avar N v * B2 N v))
        (iA2.const_mul _) (iAB'.const_mul _), integral_const_mul, integral_const_mul, integral_const_mul]
  have EV2 : ∫ v, M.kanVarRep T κ v ^ 2 ∂μK =
      σ2 ^ 2 * (∫ v, Avar N v ^ 2 ∂μK) + 2 * σ2 * K * (∫ v, Avar N v * B2 N v ∂μK) +
        K ^ 2 * (∫ v, B2 N v ^ 2 ∂μK) + L ^ 2 * (∫ v, (Rr v * Cc N v) ^ 2 ∂μK) := by
    rw [sq_exp, integral_add (f := fun v => (σ2 * Avar N v + K * B2 N v) ^ 2 +
        2 * L * ((σ2 * Avar N v + K * B2 N v) * (Rr v * Cc N v)))
      (g := fun v => L ^ 2 * (Rr v * Cc N v) ^ 2) (iW2.add (iWRC.const_mul _)) (iRC2.const_mul _),
      integral_add (f := fun v => (σ2 * Avar N v + K * B2 N v) ^ 2)
        (g := fun v => 2 * L * ((σ2 * Avar N v + K * B2 N v) * (Rr v * Cc N v))) iW2
        (iWRC.const_mul _), integral_const_mul, integral_const_mul, EW2, zX]
    ring
  -- conclusion
  have hX : MemLp (fun ω => M.oosVar κ (sampleData r ω)) 2 P :=
    (memLp_two_iff_integrable_sq hI49.aestronglyMeasurable).2 (hI2.2 aV.integrable_sq)
  refine ⟨hX, ?_⟩
  rw [variance_eq_sub hX]
  have f2 : P[(fun ω => M.oosVar κ (sampleData r ω)) ^ 2] = ∫ v, M.kanVarRep T κ v ^ 2 ∂μK := by
    rw [← hE2]; rfl
  have f1 : P[fun ω => M.oosVar κ (sampleData r ω)] = _ := hE49
  rw [f2, f1, EV2, eAB, eB2, eRC2, eSA, eSB, eSC, eBA, c51.2, c52.2, c53.2, c54.2, c55.2, c56.2,
    c57.2]
  have hL : L ^ 2 = 4 * κ ^ 2 * T * σ2 / M.gamma ^ 2 := by
    simp only [L]
    rw [div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg T), Real.sq_sqrt hσ]; ring
  rw [hL]
  simp only [K, C]
  have hTN : (N : ℝ) + 7 < T := by exact_mod_cast hT
  have h0 : (T : ℝ) - N ≠ 0 := by intro h; linarith
  have h1 : (T : ℝ) - N - 1 ≠ 0 := by intro h; linarith
  have h2 : (T : ℝ) - N - 2 ≠ 0 := by intro h; linarith
  have h3 : (T : ℝ) - N - 3 ≠ 0 := by intro h; linarith
  have h5 : (T : ℝ) - N - 5 ≠ 0 := by intro h; linarith
  have h7 : (T : ℝ) - N - 7 ≠ 0 := by intro h; linarith
  have h8 : (T : ℝ) - N + 1 ≠ 0 := by intro h; linarith
  field_simp
  ring
