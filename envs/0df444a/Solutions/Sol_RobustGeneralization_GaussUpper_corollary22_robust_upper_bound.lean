-- Prove2me | solution 1 for RobustGeneralization.GaussUpper.corollary22_robust_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T08:12:58.817722+00:00
-- url     : https://prove2.me/submissions/ac6a9b92-e70d-4968-be1f-ed87f6d8f2f9

import Mathlib
import Definitions.Def_RobustGeneralization_GaussUpper_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem rg22_mgf1 (s : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (s * x)) ∂(gaussianReal 0 1)
      = ENNReal.ofReal (Real.exp (s ^ 2 / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal s)
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))]
  congr 1
  have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) s
  simp only [mgf, id] at h
  rw [h]
  congr 1
  push_cast
  ring

theorem rg22_pi_lint {ι X : Type*} [Fintype ι] [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (f : ι → X → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ S, ∏ i, f i (S i) ∂(Measure.pi fun _ : ι => ν) = ∏ i, ∫⁻ x, f i x ∂ν := by
  have hind : iIndepFun (fun i (S : ι → X) => f i (S i)) (Measure.pi fun _ : ι => ν) :=
    iIndepFun_pi (X := fun i => f i) (fun i => (hf i).aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun i => (hf i).comp (measurable_pi_apply i))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact (measurePreserving_eval (fun _ : ι => ν) i).lintegral_comp (hf i)

theorem rg22_mgfE {d : ℕ} (h : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    ∫⁻ v, ENNReal.ofReal (Real.exp (t * inner ℝ h v)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      = ENNReal.ofReal (Real.exp (t ^ 2 * ‖h‖ ^ 2 / 2)) := by
  rw [← map_pi_eq_stdGaussian, lintegral_map (by fun_prop) (by fun_prop)]
  have hprod : ∀ x : Fin d → ℝ,
      ENNReal.ofReal (Real.exp (t * inner ℝ h (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))))
      = ∏ i, ENNReal.ofReal (Real.exp ((t * h i) * x i)) := by
    intro x
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
    congr 2
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  simp_rw [hprod]
  rw [rg22_pi_lint (gaussianReal 0 1) (fun i x => ENNReal.ofReal (Real.exp ((t * h i) * x)))
    (fun i => by fun_prop)]
  simp_rw [rg22_mgf1]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem rg22_gauss_sq_int (t : ℝ) (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (t * x ^ 2)) (gaussianReal 0 1) ∧
      ∫ x, Real.exp (t * x ^ 2) ∂(gaussianReal 0 1) = (Real.sqrt (1 - 2 * t))⁻¹ := by
  have hb : 0 < 1 / 2 - t := by linarith
  have hpt : ∀ x : ℝ, gaussianPDFReal 0 1 x * Real.exp (t * x ^ 2)
      = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * x ^ 2) := by
    intro x
    rw [gaussianPDFReal, mul_assoc, ← Real.exp_add]
    congr 2
    · simp
    · push_cast; ring
  constructor
  · rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
      integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
        (Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top))]
    have : (fun x : ℝ => (gaussianPDF 0 1 x).toReal • Real.exp (t * x ^ 2))
        = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * x ^ 2) := by
      funext x
      rw [toReal_gaussianPDF, smul_eq_mul, hpt]
    rw [this]
    exact (integrable_exp_neg_mul_sq hb).const_mul _
  · rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    simp_rw [smul_eq_mul, hpt]
    rw [integral_const_mul, integral_gaussian]
    have h2 : (0 : ℝ) < 2 * Real.pi := by positivity
    have h3 : (0 : ℝ) < 1 - 2 * t := by linarith
    rw [show Real.pi / (1 / 2 - t) = (2 * Real.pi) / (1 - 2 * t) by field_simp]
    rw [Real.sqrt_div h2.le, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.2 h2).ne', one_mul]

theorem rg22_sq1 :
    ∫⁻ x, ENNReal.ofReal (Real.exp ((1 / 4) * x ^ 2)) ∂(gaussianReal 0 1)
      ≤ ENNReal.ofReal (Real.exp (3 / 8)) := by
  obtain ⟨hi, he⟩ := rg22_gauss_sq_int (1 / 4) (by norm_num)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)), he]
  apply ENNReal.ofReal_le_ofReal
  -- (√(1/2))⁻¹ = √2 ≤ exp(3/8)
  have h1 : (Real.sqrt (1 - 2 * (1 / 4 : ℝ)))⁻¹ = Real.sqrt 2 := by
    rw [show (1 - 2 * (1 / 4 : ℝ)) = (Real.sqrt 2)⁻¹ ^ 2 by
      rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num]
    rw [Real.sqrt_sq (by positivity), inv_inv]
  rw [h1]
  have h2 : Real.sqrt 2 < 1.415 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h3 : (1.415 : ℝ) ≤ Real.exp (3 / 8) := by
    have := Real.add_one_le_exp (3 / 8 : ℝ)
    have h4 := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 3 / 8 by norm_num)
    nlinarith
  linarith

theorem rg22_sqE {d : ℕ} :
    ∫⁻ v, ENNReal.ofReal (Real.exp (‖v‖ ^ 2 / 4)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      ≤ ENNReal.ofReal (Real.exp (3 * d / 8)) := by
  rw [← map_pi_eq_stdGaussian, lintegral_map (by fun_prop) (by fun_prop)]
  have hprod : ∀ x : Fin d → ℝ,
      ENNReal.ofReal (Real.exp (‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2 / 4))
      = ∏ i, ENNReal.ofReal (Real.exp ((1 / 4) * x i ^ 2)) := by
    intro x
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum,
      EuclideanSpace.real_norm_sq_eq, Finset.sum_div]
    congr 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp
    ring
  simp_rw [hprod]
  rw [rg22_pi_lint (gaussianReal 0 1) (fun i x => ENNReal.ofReal (Real.exp ((1 / 4) * x ^ 2)))
    (fun i => by fun_prop)]
  calc ∏ i : Fin d, ∫⁻ x, ENNReal.ofReal (Real.exp ((1 / 4) * x ^ 2)) ∂(gaussianReal 0 1)
      ≤ ∏ i : Fin d, ENNReal.ofReal (Real.exp (3 / 8)) :=
        Finset.prod_le_prod' (fun i _ => rg22_sq1)
    _ = ENNReal.ofReal (Real.exp (3 * d / 8)) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
        congr 2
        ring

theorem rg22_markov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℝ)
    (hg : Measurable g) (a : ℝ) :
    μ {x | a ≤ g x} ≤ ENNReal.ofReal (Real.exp (-a)) * ∫⁻ x, ENNReal.ofReal (Real.exp (g x)) ∂μ := by
  have h1 := mul_meas_ge_le_lintegral₀ (μ := μ) (f := fun x => ENNReal.ofReal (Real.exp (g x)))
    (Real.measurable_exp.comp hg).ennreal_ofReal.aemeasurable (ENNReal.ofReal (Real.exp a))
  have hsub : {x | a ≤ g x} ⊆
      {x | ENNReal.ofReal (Real.exp a) ≤ ENNReal.ofReal (Real.exp (g x))} := by
    intro x hx
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hx)
  calc μ {x | a ≤ g x}
      ≤ μ {x | ENNReal.ofReal (Real.exp a) ≤ ENNReal.ofReal (Real.exp (g x))} := measure_mono hsub
    _ = ENNReal.ofReal (Real.exp (-a)) * (ENNReal.ofReal (Real.exp a) *
          μ {x | ENNReal.ofReal (Real.exp a) ≤ ENNReal.ofReal (Real.exp (g x))}) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        simp
    _ ≤ _ := by gcongr

theorem rg22_lab_meas : Measurable RobustGeneralization.GaussUpper.lab := measurable_of_finite _

open RobustGeneralization.GaussUpper in
theorem rg22_model_lint {d : ℕ} (θ : E d) (σ : ℝ) (F : E d × Bool → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ p, F p ∂(gaussModel θ σ) = (1 / 2 : ℝ≥0∞) * ∫⁻ v, F (θ + σ • v, true) ∂(stdGaussian (E d))
      + (1 / 2 : ℝ≥0∞) * ∫⁻ v, F (-θ + σ • v, false) ∂(stdGaussian (E d)) := by
  unfold gaussModel gaussVec
  have m1 : Measurable (fun x : E d => (x, true)) := measurable_id.prodMk measurable_const
  have m2 : Measurable (fun x : E d => (x, false)) := measurable_id.prodMk measurable_const
  have m3 : Measurable (fun v : E d => θ + σ • v) := by fun_prop
  have m4 : Measurable (fun v : E d => -θ + σ • v) := by fun_prop
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_map hF m1, lintegral_map hF m2,
    lintegral_map (show Measurable (fun a : E d => F (a, true)) from hF.comp m1) m3,
    lintegral_map (show Measurable (fun a : E d => F (a, false)) from hF.comp m2) m4]
  rfl

open RobustGeneralization.GaussUpper in
theorem rg22_zeta_meas {d : ℕ} : Measurable (fun p : E d × Bool => lab p.2 • p.1) :=
  (rg22_lab_meas.comp measurable_snd).smul measurable_fst

open RobustGeneralization.GaussUpper in
theorem rg22_model_mgf {d : ℕ} (θ : E d) (σ : ℝ) (h : E d) (t : ℝ) :
    ∫⁻ p, ENNReal.ofReal (Real.exp (t * inner ℝ (lab p.2 • p.1) h)) ∂(gaussModel θ σ)
      = ENNReal.ofReal (Real.exp (t * inner ℝ θ h + t ^ 2 * σ ^ 2 * ‖h‖ ^ 2 / 2)) := by
  have hF : Measurable (fun p : E d × Bool =>
      ENNReal.ofReal (Real.exp (t * inner ℝ (lab p.2 • p.1) h))) :=
    (Real.measurable_exp.comp (measurable_const.mul
      (rg22_zeta_meas.inner measurable_const))).ennreal_ofReal
  rw [rg22_model_lint θ σ _ hF]
  have e1 : ∀ v : E d, ENNReal.ofReal (Real.exp (t * inner ℝ
        (lab (θ + σ • v, true).2 • (θ + σ • v, true).1) h))
      = ENNReal.ofReal (Real.exp (t * inner ℝ θ h)) *
        ENNReal.ofReal (Real.exp ((t * σ) * inner ℝ h v)) := by
    intro v
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    simp only [lab, one_smul, inner_add_left, inner_smul_left, real_inner_comm h v]
    simp only [conj_trivial]
    ring
  have e2 : ∀ v : E d, ENNReal.ofReal (Real.exp (t * inner ℝ
        (lab (-θ + σ • v, false).2 • (-θ + σ • v, false).1) h))
      = ENNReal.ofReal (Real.exp (t * inner ℝ θ h)) *
        ENNReal.ofReal (Real.exp ((-(t * σ)) * inner ℝ h v)) := by
    intro v
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    simp only [lab, neg_smul, one_smul, neg_add, neg_neg, inner_add_left, inner_neg_left,
      inner_smul_left, real_inner_comm h v]
    simp only [conj_trivial]
    ring
  simp_rw [e1, e2]
  rw [lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop), rg22_mgfE,
    rg22_mgfE, neg_sq, ← mul_add, ← two_mul, ← mul_assoc, one_div,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

theorem rg22_l1 {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) : ∑ i, |w i| ≤ Real.sqrt d * ‖w‖ := by
  have h1 : (∑ i, |w i| * 1) ^ 2 ≤ (∑ i, |w i| ^ 2) * (∑ i : Fin d, (1 : ℝ) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, sq_abs] at h1
  have h2 : ‖w‖ ^ 2 = ∑ i, w i ^ 2 := EuclideanSpace.real_norm_sq_eq w
  have h3 : (Real.sqrt d * ‖w‖) ^ 2 = d * ‖w‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  refine (pow_le_pow_iff_left₀ (Finset.sum_nonneg (fun i _ => abs_nonneg _)) (by positivity)
    two_ne_zero).1 ?_
  rw [h3, h2]
  linarith

open RobustGeneralization.GaussUpper in
theorem rg22_chern {d : ℕ} (w : E d) (hw : w ≠ 0) :
    stdGaussian (E d) {v | 4 * ‖w‖ ≤ inner ℝ w v} ≤ ENNReal.ofReal (Real.exp (-8)) := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  set lam : ℝ := 4 / ‖w‖ with hlam
  have hl0 : 0 ≤ lam := by positivity
  have hl1 : lam * (4 * ‖w‖) = 16 := by rw [hlam]; field_simp; ring
  have hsub : {v : E d | 4 * ‖w‖ ≤ inner ℝ w v} ⊆ {v | 16 ≤ lam * inner ℝ w v} := by
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv ⊢
    have := mul_le_mul_of_nonneg_left hv hl0
    linarith
  calc stdGaussian (E d) {v | 4 * ‖w‖ ≤ inner ℝ w v}
      ≤ stdGaussian (E d) {v | 16 ≤ lam * inner ℝ w v} := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-16)) *
          ∫⁻ v, ENNReal.ofReal (Real.exp (lam * inner ℝ w v)) ∂(stdGaussian (E d)) :=
        rg22_markov _ _ (by fun_prop) 16
    _ = ENNReal.ofReal (Real.exp (-8)) := by
        rw [rg22_mgfE, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        rw [hlam]
        field_simp
        ring

theorem rg22_exp8 : Real.exp (-8) ≤ 1 / 100 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have h2 : Real.exp 8 = Real.exp 1 ^ 8 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h3 : (256 : ℝ) ≤ Real.exp 8 := by
    rw [h2]
    calc (256 : ℝ) = 2 ^ 8 := by norm_num
      _ ≤ Real.exp 1 ^ 8 := pow_le_pow_left₀ (by norm_num) h1 8
  rw [Real.exp_neg]
  rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  linarith

open RobustGeneralization.GaussUpper in
theorem rg22_robust {d : ℕ} (θ : E d) (σ : ℝ) (hσ : 0 < σ) (ε : ℝ) (w : E d) (hw : w ≠ 0)
    (hmarg : (max ε 0 * Real.sqrt d + 4 * σ) * ‖w‖ ≤ inner ℝ w θ) :
    robustErr (gaussModel θ σ) (linClf w) ε ≤ ENNReal.ofReal (1 / 100) := by
  set L : ℝ := max ε 0 * ∑ i, |w i| with hL
  have hL' : L ≤ max ε 0 * Real.sqrt d * ‖w‖ := by
    rw [hL, mul_assoc]
    exact mul_le_mul_of_nonneg_left (rg22_l1 w) (le_max_right _ _)
  set T : Set (E d × Bool) := {p | lab p.2 * inner ℝ w p.1 ≤ L} with hT
  have hTm : MeasurableSet T := by
    apply measurableSet_le
    · exact (rg22_lab_meas.comp measurable_snd).mul (measurable_const.inner measurable_fst)
    · exact measurable_const
  have hsub : {p : E d × Bool | ∃ x' ∈ linfBall p.1 ε, linClf w x' ≠ p.2} ⊆ T := by
    rintro ⟨x, y⟩ ⟨x', hx', hne⟩
    simp only [linfBall, Set.mem_ofPred_eq] at hx'
    have key : |inner ℝ w x' - inner ℝ w x| ≤ L := by
      rw [← inner_sub_right]
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, PiLp.sub_apply]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [hL, Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [abs_mul]
      have h1 := (hx' i).trans (le_max_left ε 0)
      nlinarith [abs_nonneg (w i), abs_nonneg (x' i - x i)]
    have hk := abs_le.1 key
    simp only [hT, Set.mem_ofPred_eq]
    cases y with
    | true =>
      simp [linClf] at hne
      simp only [lab, one_mul]
      linarith
    | false =>
      simp [linClf] at hne
      simp only [lab]
      linarith
  have hG : gaussModel θ σ T
      = (1 / 2 : ℝ≥0∞) * stdGaussian (E d) {v | lab true * inner ℝ w (θ + σ • v) ≤ L}
        + (1 / 2 : ℝ≥0∞) * stdGaussian (E d) {v | lab false * inner ℝ w (-θ + σ • v) ≤ L} := by
    have m1 : Measurable (fun x : E d => (x, true)) := measurable_id.prodMk measurable_const
    have m2 : Measurable (fun x : E d => (x, false)) := measurable_id.prodMk measurable_const
    have m3 : Measurable (fun v : E d => θ + σ • v) := by fun_prop
    have m4 : Measurable (fun v : E d => -θ + σ • v) := by fun_prop
    unfold gaussModel gaussVec
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, Measure.map_apply m1 hTm,
      Measure.map_apply m2 hTm, Measure.map_apply m3 (hTm.preimage m1),
      Measure.map_apply m4 (hTm.preimage m2)]
    rfl
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hA : stdGaussian (E d) {v | lab true * inner ℝ w (θ + σ • v) ≤ L}
      ≤ ENNReal.ofReal (Real.exp (-8)) := by
    refine le_trans (measure_mono ?_) ((rg22_chern (-w) (neg_ne_zero.2 hw)))
    intro v hv
    simp only [Set.mem_ofPred_eq, lab, one_mul, inner_add_right, inner_smul_right] at hv ⊢
    rw [norm_neg, inner_neg_left]
    have h2 : σ * (4 * ‖w‖) ≤ σ * (-inner ℝ w v) := by nlinarith
    exact le_of_mul_le_mul_left h2 hσ
  have hB : stdGaussian (E d) {v | lab false * inner ℝ w (-θ + σ • v) ≤ L}
      ≤ ENNReal.ofReal (Real.exp (-8)) := by
    refine le_trans (measure_mono ?_) ((rg22_chern w hw))
    intro v hv
    simp only [Set.mem_ofPred_eq, lab, inner_add_right, inner_smul_right, inner_neg_right] at hv ⊢
    have h2 : σ * (4 * ‖w‖) ≤ σ * (inner ℝ w v) := by nlinarith
    exact le_of_mul_le_mul_left h2 hσ
  calc robustErr (gaussModel θ σ) (linClf w) ε ≤ gaussModel θ σ T := measure_mono hsub
    _ = _ := hG
    _ ≤ (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-8))
          + (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-8)) := by gcongr
    _ = ENNReal.ofReal (Real.exp (-8)) := by
        rw [← add_mul, ENNReal.add_halves, one_mul]
    _ ≤ ENNReal.ofReal (1 / 100) := ENNReal.ofReal_le_ofReal rg22_exp8

open RobustGeneralization.GaussUpper in
theorem rg22_zbar_inner {d n : ℕ} (S : Fin n → E d × Bool) (h : E d) :
    inner ℝ (zbar S) h = (n : ℝ)⁻¹ * ∑ i, inner ℝ (lab (S i).2 • (S i).1) h := by
  simp only [zbar, inner_smul_left, sum_inner, conj_trivial]

open RobustGeneralization.GaussUpper in
theorem rg22_zbar_meas {d n : ℕ} : Measurable (fun S : Fin n → E d × Bool => zbar S) := by
  have h : Measurable (fun S : Fin n → E d × Bool => ∑ i, lab (S i).2 • (S i).1) :=
    Finset.measurable_sum _ (fun i _ => (rg22_zeta_meas (d := d)).comp (measurable_pi_apply i))
  exact h.const_smul ((n : ℝ)⁻¹)

open RobustGeneralization.GaussUpper in
theorem rg22_prob {d : ℕ} (θ : E d) (σ : ℝ) : IsProbabilityMeasure (gaussModel θ σ) := by
  constructor
  have h := rg22_model_lint θ σ (fun _ => (1 : ℝ≥0∞)) measurable_const
  simp only [lintegral_const, measure_univ, mul_one, one_mul] at h
  rw [ENNReal.add_halves] at h
  exact h

open RobustGeneralization.GaussUpper in
theorem rg22_tailA {d n : ℕ} (θ : E d) (hθ : ‖θ‖ = Real.sqrt d) (σ : ℝ) (hσ : 0 < σ)
    (hn : 1 ≤ n) :
    (Measure.pi fun _ : Fin n => gaussModel θ σ) {S | inner ℝ (zbar S) θ ≤ d / 2}
      ≤ ENNReal.ofReal (Real.exp (-(d : ℝ) / (8 * (σ ^ 2 + 1)))) := by
  have := rg22_prob θ σ
  set lam : ℝ := 1 / (2 * σ ^ 2) with hlam
  have hl0 : 0 < lam := by positivity
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set g : (Fin n → E d × Bool) → ℝ :=
    fun S => ∑ i, (-lam) * inner ℝ (lab (S i).2 • (S i).1) θ with hg
  have hfm : ∀ i : Fin n, Measurable (fun p : E d × Bool =>
      ENNReal.ofReal (Real.exp ((-lam) * inner ℝ (lab p.2 • p.1) θ))) := fun i =>
    (Real.measurable_exp.comp (measurable_const.mul
      (rg22_zeta_meas.inner measurable_const))).ennreal_ofReal
  have hgm : Measurable g := Finset.measurable_sum _ (fun i _ => measurable_const.mul
    ((rg22_zeta_meas.comp (measurable_pi_apply i)).inner measurable_const))
  have hsub : {S : Fin n → E d × Bool | inner ℝ (zbar S) θ ≤ d / 2}
      ⊆ {S | -(lam * n * d / 2) ≤ g S} := by
    intro S hS
    simp only [Set.mem_ofPred_eq, rg22_zbar_inner] at hS ⊢
    simp only [hg, ← Finset.mul_sum]
    have h1 : ∑ i, inner ℝ (lab (S i).2 • (S i).1) θ ≤ n * (d / 2) := by
      rw [inv_mul_le_iff₀ hnpos] at hS
      linarith
    nlinarith
  have hθθ : inner ℝ θ θ = (d : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hθ, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hprod : ∀ S : Fin n → E d × Bool, ENNReal.ofReal (Real.exp (g S))
      = ∏ i, ENNReal.ofReal (Real.exp ((-lam) * inner ℝ (lab (S i).2 • (S i).1) θ)) := by
    intro S
    rw [hg, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  calc (Measure.pi fun _ : Fin n => gaussModel θ σ) {S | inner ℝ (zbar S) θ ≤ d / 2}
      ≤ (Measure.pi fun _ : Fin n => gaussModel θ σ) {S | -(lam * n * d / 2) ≤ g S} :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-(-(lam * n * d / 2)))) *
          ∫⁻ S, ENNReal.ofReal (Real.exp (g S)) ∂(Measure.pi fun _ : Fin n => gaussModel θ σ) :=
        rg22_markov _ g hgm _
    _ = ENNReal.ofReal (Real.exp (lam * n * d / 2)) *
          (ENNReal.ofReal (Real.exp ((-lam) * d + (-lam) ^ 2 * σ ^ 2 * d / 2))) ^ n := by
        simp_rw [hprod]
        rw [rg22_pi_lint (gaussModel θ σ)
          (fun i p => ENNReal.ofReal (Real.exp ((-lam) * inner ℝ (lab p.2 • p.1) θ))) hfm]
        simp_rw [rg22_model_mgf]
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, neg_neg, hθθ, hθ,
          Real.sq_sqrt (Nat.cast_nonneg _)]
    _ = ENNReal.ofReal (Real.exp (-(n * d / (8 * σ ^ 2)))) := by
        rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        rw [hlam]
        field_simp
        ring
    _ ≤ ENNReal.ofReal (Real.exp (-(d : ℝ) / (8 * (σ ^ 2 + 1)))) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.2
        rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        have h5 : σ ^ 2 ≤ n * (σ ^ 2 + 1) := by nlinarith [sq_nonneg σ]
        nlinarith [mul_le_mul_of_nonneg_left h5 hd0]

open RobustGeneralization.GaussUpper in
theorem rg22_tailB {d n : ℕ} (θ : E d) (σ : ℝ) (hσ : 0 < σ) (hn : 1 ≤ n) :
    (Measure.pi fun _ : Fin n => gaussModel θ σ) {S | 2 * σ ^ 2 * d / n ≤ ‖zbar S - θ‖ ^ 2}
      ≤ ENNReal.ofReal (Real.exp (-(d : ℝ) / (8 * (σ ^ 2 + 1)))) := by
  have := rg22_prob θ σ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set a : ℝ := Real.sqrt (n / (2 * σ ^ 2)) with ha
  have ha2 : a ^ 2 = n / (2 * σ ^ 2) := Real.sq_sqrt (by positivity)
  set g : (Fin n → E d × Bool) → ℝ := fun S => a ^ 2 * ‖zbar S - θ‖ ^ 2 / 2 with hg
  have hgm : Measurable g :=
    (measurable_const.mul ((rg22_zbar_meas.sub measurable_const).norm.pow_const 2)).div_const 2
  have hsub : {S : Fin n → E d × Bool | 2 * σ ^ 2 * d / n ≤ ‖zbar S - θ‖ ^ 2}
      ⊆ {S | (d : ℝ) / 2 ≤ g S} := by
    intro S hS
    simp only [Set.mem_ofPred_eq] at hS ⊢
    simp only [hg]
    have h1 : a ^ 2 * (2 * σ ^ 2 * d / n) = d := by
      rw [ha2]
      field_simp
    have h2 := mul_le_mul_of_nonneg_left hS (sq_nonneg a)
    linarith
  have hfm : ∀ v : E d, ∀ i : Fin n, Measurable (fun p : E d × Bool =>
      ENNReal.ofReal (Real.exp ((a / n) * inner ℝ (lab p.2 • p.1) v))) := fun v i =>
    (Real.measurable_exp.comp (measurable_const.mul
      (rg22_zeta_meas.inner measurable_const))).ennreal_ofReal
  have hkey : ∫⁻ S, ENNReal.ofReal (Real.exp (g S)) ∂(Measure.pi fun _ : Fin n => gaussModel θ σ)
      ≤ ENNReal.ofReal (Real.exp (3 * d / 8)) := by
    have hHS : ∀ S : Fin n → E d × Bool, ENNReal.ofReal (Real.exp (g S))
        = ∫⁻ v, ENNReal.ofReal (Real.exp (a * inner ℝ (zbar S - θ) v)) ∂(stdGaussian (E d)) := by
      intro S
      rw [rg22_mgfE]
    simp_rw [hHS]
    have hmeas : Measurable (Function.uncurry fun (S : Fin n → E d × Bool) (v : E d) =>
        ENNReal.ofReal (Real.exp (a * inner ℝ (zbar S - θ) v))) :=
      (Real.measurable_exp.comp (measurable_const.mul
        (((rg22_zbar_meas.comp measurable_fst).sub measurable_const).inner
          measurable_snd))).ennreal_ofReal
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    have hin : ∀ v : E d, ∫⁻ S, ENNReal.ofReal (Real.exp (a * inner ℝ (zbar S - θ) v))
        ∂(Measure.pi fun _ : Fin n => gaussModel θ σ) = ENNReal.ofReal (Real.exp (‖v‖ ^ 2 / 4)) := by
      intro v
      have hprod : ∀ S : Fin n → E d × Bool, ENNReal.ofReal (Real.exp (a * inner ℝ (zbar S - θ) v))
          = ENNReal.ofReal (Real.exp (-(a * inner ℝ θ v))) *
            ∏ i, ENNReal.ofReal (Real.exp ((a / n) * inner ℝ (lab (S i).2 • (S i).1) v)) := by
        intro S
        rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        rw [inner_sub_left, rg22_zbar_inner, ← Finset.mul_sum]
        field_simp
        ring
      have hPm : Measurable (fun S : Fin n → E d × Bool =>
          ∏ i, ENNReal.ofReal (Real.exp ((a / n) * inner ℝ (lab (S i).2 • (S i).1) v))) :=
        Finset.measurable_prod _ (fun i _ => (hfm v i).comp (measurable_pi_apply i))
      simp_rw [hprod]
      rw [lintegral_const_mul _ hPm,
        rg22_pi_lint (gaussModel θ σ)
          (fun i p => ENNReal.ofReal (Real.exp ((a / n) * inner ℝ (lab p.2 • p.1) v))) (hfm v)]
      simp_rw [rg22_model_mgf]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      have e1 : -(a * inner ℝ θ v) + (n : ℝ) * (a / n * inner ℝ θ v + (a / n) ^ 2 * σ ^ 2 * ‖v‖ ^ 2 / 2)
          = a ^ 2 * σ ^ 2 * ‖v‖ ^ 2 / (2 * n) := by
        field_simp
        ring
      rw [e1, ha2]
      field_simp
      ring
    simp_rw [hin]
    exact rg22_sqE
  calc (Measure.pi fun _ : Fin n => gaussModel θ σ) {S | 2 * σ ^ 2 * d / n ≤ ‖zbar S - θ‖ ^ 2}
      ≤ (Measure.pi fun _ : Fin n => gaussModel θ σ) {S | (d : ℝ) / 2 ≤ g S} := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-((d : ℝ) / 2))) *
          ∫⁻ S, ENNReal.ofReal (Real.exp (g S)) ∂(Measure.pi fun _ : Fin n => gaussModel θ σ) :=
        rg22_markov _ g hgm _
    _ ≤ ENNReal.ofReal (Real.exp (-((d : ℝ) / 2))) * ENNReal.ofReal (Real.exp (3 * d / 8)) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (-((d : ℝ) / 8))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        ring
    _ ≤ ENNReal.ofReal (Real.exp (-(d : ℝ) / (8 * (σ ^ 2 + 1)))) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.2
        rw [neg_div, neg_le_neg_iff]
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg σ]

theorem rg22_arith (d n σ ε q r : ℝ) (hq1 : 1 ≤ q) (hd : d = q ^ 4) (hσ : 0 < σ)
    (hσ' : σ ≤ 1 / 32 * q)
    (hn : ε ≤ 1 / 4 * q⁻¹ ∨ (1 / 4 * q⁻¹ ≤ ε ∧ ε ≤ 1 / 4 ∧ 64 * ε ^ 2 * q ^ 2 ≤ n))
    (hn1 : 1 ≤ n) (hr0 : 0 ≤ r) (hr : r ^ 2 ≤ 2 * σ ^ 2 * d / n) :
    (max ε 0 * q ^ 2 + 4 * σ) * (q ^ 2 + r) ≤ q ^ 4 / 2 := by
  have hnpos : 0 < n := by linarith
  have hq0 : 0 < q := by linarith
  have hr' : r ^ 2 * n ≤ 2 * σ ^ 2 * q ^ 4 := by
    rw [hd, le_div_iff₀ hnpos] at hr
    exact hr
  have hs2 : σ ^ 2 ≤ q ^ 2 / 1024 := by nlinarith
  have hqi : q * q⁻¹ = 1 := mul_inv_cancel₀ hq0.ne'
  rcases hn with he | ⟨he1, he2, hn2⟩
  · have hm : max ε 0 * q ≤ 1 / 4 := by
      rcases le_total ε 0 with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]
        have := mul_le_mul_of_nonneg_right he hq0.le
        nlinarith
    have hm0 : 0 ≤ max ε 0 := le_max_right _ _
    have hK : max ε 0 * q ^ 2 + 4 * σ ≤ 3 / 8 * q := by nlinarith
    have hr2 : r ^ 2 ≤ (q ^ 3 / 16) ^ 2 := by
      have h1 : r ^ 2 ≤ r ^ 2 * n := by nlinarith [sq_nonneg r]
      have h2 : 2 * σ ^ 2 * q ^ 4 ≤ 2 * (q ^ 2 / 1024) * q ^ 4 := by
        have : 0 ≤ q ^ 4 := by positivity
        nlinarith
      nlinarith
    have hr3 : r ≤ q ^ 3 / 16 :=
      (pow_le_pow_iff_left₀ hr0 (by positivity) two_ne_zero).1 hr2
    have hK0 : 0 ≤ max ε 0 * q ^ 2 + 4 * σ := by positivity
    calc (max ε 0 * q ^ 2 + 4 * σ) * (q ^ 2 + r) ≤ (3 / 8 * q) * (q ^ 2 + q ^ 3 / 16) := by
          apply mul_le_mul hK (by linarith) (by positivity) (by positivity)
      _ ≤ q ^ 4 / 2 := by
          have h3 : 0 ≤ q ^ 3 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hq1 h3]
  · have heq : 1 / 4 ≤ ε * q := by
      have := mul_le_mul_of_nonneg_right he1 hq0.le
      nlinarith
    have hε0 : 0 < ε := by
      by_contra hc
      have hc' : ε ≤ 0 := not_lt.1 hc
      nlinarith
    rw [max_eq_left hε0.le]
    have hK : ε * q ^ 2 + 4 * σ ≤ 3 / 2 * ε * q ^ 2 := by
      have : q / 4 ≤ ε * q ^ 2 := by nlinarith
      nlinarith
    have hre : r * ε ≤ q ^ 2 / 100 := by
      have h1 : r ^ 2 * (64 * ε ^ 2 * q ^ 2) ≤ r ^ 2 * n :=
        mul_le_mul_of_nonneg_left hn2 (sq_nonneg r)
      have h2 : 2 * σ ^ 2 * q ^ 4 ≤ 2 * (q ^ 2 / 1024) * q ^ 4 := by
        have : 0 ≤ q ^ 4 := by positivity
        nlinarith
      have hq2 : 0 < q ^ 2 := by positivity
      have h3 : (r * ε) ^ 2 * (64 * q ^ 2) ≤ q ^ 6 / 512 := by nlinarith
      have h4 : (r * ε) ^ 2 ≤ (q ^ 2 / 100) ^ 2 := by
        by_contra hc
        have hc' := not_le.1 hc
        have h5 : (q ^ 2 / 100) ^ 2 * (64 * q ^ 2) < (r * ε) ^ 2 * (64 * q ^ 2) :=
          mul_lt_mul_of_pos_right hc' (by positivity)
        nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h4
    calc (ε * q ^ 2 + 4 * σ) * (q ^ 2 + r) ≤ (3 / 2 * ε * q ^ 2) * (q ^ 2 + r) := by
          apply mul_le_mul_of_nonneg_right hK (by positivity)
      _ = 3 / 2 * ε * q ^ 4 + 3 / 2 * q ^ 2 * (r * ε) := by ring
      _ ≤ 3 / 2 * (1 / 4) * q ^ 4 + 3 / 2 * q ^ 2 * (q ^ 2 / 100) := by
          have : 0 ≤ q ^ 4 := by positivity
          have : 0 ≤ q ^ 2 := by positivity
          gcongr
      _ ≤ q ^ 4 / 2 := by
          have : 0 ≤ q ^ 4 := by positivity
          nlinarith

open MeasureTheory ProbabilityTheory RobustGeneralization.GaussUpper in
theorem solution (d n : ℕ) (θ : E d) (hθ : ‖θ‖ = Real.sqrt d) (σ : ℝ)
    (hσ : 0 < σ) (hσ' : σ ≤ (1 / 32) * (d : ℝ) ^ ((1 : ℝ) / 4)) (ε : ℝ)
    (hn : (ε ≤ (1 / 4) * (d : ℝ) ^ (-(1 : ℝ) / 4) ∧ 1 ≤ n) ∨
      ((1 / 4) * (d : ℝ) ^ (-(1 : ℝ) / 4) ≤ ε ∧ ε ≤ 1 / 4 ∧
        64 * ε ^ 2 * Real.sqrt d ≤ n)) :
    (Measure.pi fun _ : Fin n => gaussModel θ σ)
        {S | ENNReal.ofReal (1 / 100) < robustErr (gaussModel θ σ) (linClf (what S)) ε} ≤
      ENNReal.ofReal (2 * Real.exp (-(d : ℝ) / (8 * (σ ^ 2 + 1)))) := by
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h
      rw [Nat.cast_zero, Real.zero_rpow (by norm_num), mul_zero] at hσ'
      linarith
    · exact h
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  set q : ℝ := (d : ℝ) ^ ((1 : ℝ) / 4) with hq
  have hq1 : 1 ≤ q := Real.one_le_rpow hdR (by norm_num)
  have hq4 : q ^ 4 = d := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hsq : Real.sqrt d = q ^ 2 := by
    rw [← hq4, show q ^ 4 = (q ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hqinv : (d : ℝ) ^ (-(1 : ℝ) / 4) = q⁻¹ := by
    rw [hq, ← Real.rpow_neg (Nat.cast_nonneg _)]
    congr 1
    ring
  rw [hqinv, hsq] at hn
  have hn1 : 1 ≤ n := by
    rcases hn with ⟨_, h⟩ | ⟨h1, _, h3⟩
    · exact h
    · have hq0 : 0 < q := by linarith
      have heq : 1 / 4 ≤ ε * q := by
        have := mul_le_mul_of_nonneg_right h1 hq0.le
        rw [mul_assoc, inv_mul_cancel₀ hq0.ne', mul_one] at this
        exact this
      have h4 : (4 : ℝ) ≤ n := by nlinarith
      have h5 : (1 : ℝ) ≤ n := by linarith
      exact_mod_cast h5
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hincl : {S : Fin n → E d × Bool | ENNReal.ofReal (1 / 100) <
        robustErr (gaussModel θ σ) (linClf (what S)) ε}
      ⊆ {S | inner ℝ (zbar S) θ ≤ d / 2} ∪ {S | 2 * σ ^ 2 * d / n ≤ ‖zbar S - θ‖ ^ 2} := by
    intro S hS
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hc
    obtain ⟨hA, hB⟩ := hc
    simp only [Set.mem_ofPred_eq] at hS
    refine (not_lt.2 ?_) hS
    have hz0 : zbar S ≠ 0 := by
      intro h0
      rw [h0, inner_zero_left] at hA
      linarith
    have hzn : 0 < ‖zbar S‖ := norm_pos_iff.2 hz0
    have har := rg22_arith (d : ℝ) (n : ℝ) σ ε q ‖zbar S - θ‖ hq1 hq4.symm hσ hσ' (hn.imp (fun h => h.1) id) hnR
      (norm_nonneg _) hB.le
    have hnorm : ‖zbar S‖ ≤ q ^ 2 + ‖zbar S - θ‖ := by
      calc ‖zbar S‖ = ‖θ + (zbar S - θ)‖ := by congr 1; abel
        _ ≤ ‖θ‖ + ‖zbar S - θ‖ := norm_add_le _ _
        _ = q ^ 2 + ‖zbar S - θ‖ := by rw [hθ, hsq]
    have hK0 : 0 ≤ max ε 0 * q ^ 2 + 4 * σ := by positivity
    have hmarg0 : (max ε 0 * q ^ 2 + 4 * σ) * ‖zbar S‖ ≤ inner ℝ (zbar S) θ := by
      calc (max ε 0 * q ^ 2 + 4 * σ) * ‖zbar S‖
          ≤ (max ε 0 * q ^ 2 + 4 * σ) * (q ^ 2 + ‖zbar S - θ‖) :=
            mul_le_mul_of_nonneg_left hnorm hK0
        _ ≤ q ^ 4 / 2 := har
        _ = d / 2 := by rw [hq4]
        _ ≤ inner ℝ (zbar S) θ := hA.le
    apply rg22_robust θ σ hσ ε (what S)
    · simp only [what]
      exact smul_ne_zero (inv_ne_zero hzn.ne') hz0
    · simp only [what]
      rw [norm_smul, inner_smul_left, hsq, norm_inv, norm_norm, inv_mul_cancel₀ hzn.ne',
        mul_one, conj_trivial, le_inv_mul_iff₀ hzn, mul_comm ‖zbar S‖]
      exact hmarg0
  calc (Measure.pi fun _ : Fin n => gaussModel θ σ)
        {S | ENNReal.ofReal (1 / 100) < robustErr (gaussModel θ σ) (linClf (what S)) ε}
      ≤ (Measure.pi fun _ : Fin n => gaussModel θ σ)
          ({S | inner ℝ (zbar S) θ ≤ d / 2} ∪ {S | 2 * σ ^ 2 * d / n ≤ ‖zbar S - θ‖ ^ 2}) :=
        measure_mono hincl
    _ ≤ (Measure.pi fun _ : Fin n => gaussModel θ σ) {S | inner ℝ (zbar S) θ ≤ d / 2}
        + (Measure.pi fun _ : Fin n => gaussModel θ σ)
            {S | 2 * σ ^ 2 * d / n ≤ ‖zbar S - θ‖ ^ 2} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(d : ℝ) / (8 * (σ ^ 2 + 1))))
        + ENNReal.ofReal (Real.exp (-(d : ℝ) / (8 * (σ ^ 2 + 1)))) :=
        add_le_add (rg22_tailA θ hθ σ hσ hn1) (rg22_tailB θ σ hσ hn1)
    _ = ENNReal.ofReal (2 * Real.exp (-(d : ℝ) / (8 * (σ ^ 2 + 1)))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, two_mul]
