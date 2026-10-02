-- Prove2me | solution 1 for RobustGeneralization.GaussUpper.lemma20_lp_robust_error_linear
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T08:22:15.876561+00:00
-- url     : https://prove2.me/submissions/5f595a4a-ab4c-477c-b092-3b81452571e5

import Mathlib
import Definitions.Def_RobustGeneralization_GaussUpper_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem l20_mgf1 (s : ℝ) :
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

theorem l20_pi_lint {ι X : Type*} [Fintype ι] [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (f : ι → X → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ S, ∏ i, f i (S i) ∂(Measure.pi fun _ : ι => ν) = ∏ i, ∫⁻ x, f i x ∂ν := by
  have hind : iIndepFun (fun i (S : ι → X) => f i (S i)) (Measure.pi fun _ : ι => ν) :=
    iIndepFun_pi (X := fun i => f i) (fun i => (hf i).aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun i => (hf i).comp (measurable_pi_apply i))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact (measurePreserving_eval (fun _ : ι => ν) i).lintegral_comp (hf i)

theorem l20_mgfE {d : ℕ} (h : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
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
  rw [l20_pi_lint (gaussianReal 0 1) (fun i x => ENNReal.ofReal (Real.exp ((t * h i) * x)))
    (fun i => by fun_prop)]
  simp_rw [l20_mgf1]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring


theorem l20_markov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℝ)
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

theorem l20_lab_meas : Measurable RobustGeneralization.GaussUpper.lab := measurable_of_finite _
open RobustGeneralization.GaussUpper in
theorem l20_chern {d : ℕ} (w : E d) (hw : w ≠ 0) (a : ℝ) (ha : 0 ≤ a) :
    stdGaussian (E d) {v | a ≤ inner ℝ w v}
      ≤ ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * ‖w‖ ^ 2)))) := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  set lam : ℝ := a / ‖w‖ ^ 2 with hlam
  have hl0 : 0 ≤ lam := by positivity
  have hsub : {v : E d | a ≤ inner ℝ w v} ⊆ {v | lam * a ≤ lam * inner ℝ w v} := by
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv ⊢
    exact mul_le_mul_of_nonneg_left hv hl0
  calc stdGaussian (E d) {v | a ≤ inner ℝ w v}
      ≤ stdGaussian (E d) {v | lam * a ≤ lam * inner ℝ w v} := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-(lam * a))) *
          ∫⁻ v, ENNReal.ofReal (Real.exp (lam * inner ℝ w v)) ∂(stdGaussian (E d)) :=
        l20_markov _ _ (by fun_prop) (lam * a)
    _ = ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * ‖w‖ ^ 2)))) := by
        rw [l20_mgfE, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        rw [hlam]
        field_simp
        ring


open RobustGeneralization.GaussUpper in
theorem l20_lp_smul {d : ℕ} (p : ℝ≥0∞) (hp : 1 ≤ p) (c : ℝ) (u : E d) :
    RobustGeneralization.GaussUpper.lpNorm p (c • u) = |c| * RobustGeneralization.GaussUpper.lpNorm p u := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  unfold RobustGeneralization.GaussUpper.lpNorm
  rw [WithLp.ofLp_smul, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

open RobustGeneralization.GaussUpper in
theorem l20_lp_neg {d : ℕ} (p : ℝ≥0∞) (hp : 1 ≤ p) (u : E d) :
    RobustGeneralization.GaussUpper.lpNorm p (-u) = RobustGeneralization.GaussUpper.lpNorm p u := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  unfold RobustGeneralization.GaussUpper.lpNorm
  rw [WithLp.ofLp_neg, WithLp.toLp_neg, norm_neg]

open RobustGeneralization.GaussUpper in
theorem l20_bdd {d : ℕ} (p : ℝ≥0∞) (hp : 1 ≤ p) (w : E d) :
    BddAbove {t | ∃ v : E d, RobustGeneralization.GaussUpper.lpNorm p v ≤ 1 ∧ t = inner ℝ w v} := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  refine ⟨∑ i, |w i|, ?_⟩
  rintro t ⟨v, hv, rfl⟩
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  refine (Finset.sum_le_sum (fun i _ => le_abs_self _)).trans ?_
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [abs_mul]
  have h1 : |v i| ≤ 1 := by
    have := PiLp.norm_apply_le (WithLp.toLp p (WithLp.ofLp v) : PiLp p (fun _ : Fin d => ℝ)) i
    rw [Real.norm_eq_abs] at this
    exact this.trans hv
  nlinarith [abs_nonneg (w i), abs_nonneg (v i)]

open RobustGeneralization.GaussUpper in
theorem l20_key {d : ℕ} (p : ℝ≥0∞) (hp : 1 ≤ p) (ε : ℝ) (hε : 0 ≤ ε) (w u : E d)
    (hu : RobustGeneralization.GaussUpper.lpNorm p u ≤ ε) : inner ℝ w u ≤ ε * dualNorm p w := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  rcases hε.eq_or_lt with h0 | hpos
  · subst h0
    have hz : (WithLp.toLp p (WithLp.ofLp u) : PiLp p (fun _ : Fin d => ℝ)) = 0 :=
      norm_le_zero_iff.1 hu
    have hu0 : u = 0 := by
      ext i
      have := congrArg (fun f : PiLp p (fun _ : Fin d => ℝ) => f i) hz
      simpa using this
    simp [hu0]
  · have hv : RobustGeneralization.GaussUpper.lpNorm p (ε⁻¹ • u) ≤ 1 := by
      rw [l20_lp_smul p hp, abs_of_pos (inv_pos.2 hpos)]
      calc ε⁻¹ * RobustGeneralization.GaussUpper.lpNorm p u ≤ ε⁻¹ * ε := by gcongr
        _ = 1 := inv_mul_cancel₀ hpos.ne'
    have hle : inner ℝ w (ε⁻¹ • u) ≤ dualNorm p w :=
      le_csSup (l20_bdd p hp w) ⟨_, hv, rfl⟩
    rw [inner_smul_right] at hle
    have : inner ℝ w u = ε * (ε⁻¹ * inner ℝ w u) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hle hpos.le


open MeasureTheory ProbabilityTheory RobustGeneralization.GaussUpper in open scoped ENNReal in
theorem solution (d : ℕ) (θ : E d) (σ : ℝ) (hσ : 0 < σ) (p : ℝ≥0∞)
    (hp : 1 ≤ p) (ε : ℝ) (hε : 0 ≤ ε) (w : E d) (hw : ‖w‖ = 1)
    (hwθ : ε * dualNorm p w ≤ inner ℝ w θ) :
    robustErrP p (gaussModel θ σ) (linClf w) ε ≤
      ENNReal.ofReal
        (Real.exp (-(inner ℝ w θ - ε * dualNorm p w) ^ 2 / (2 * σ ^ 2))) := by
  set L : ℝ := ε * dualNorm p w with hL
  have hwne : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; exact zero_ne_one hw
  set T : Set (E d × Bool) := {q | lab q.2 * inner ℝ w q.1 ≤ L} with hT
  have hTm : MeasurableSet T := by
    apply measurableSet_le
    · exact (l20_lab_meas.comp measurable_snd).mul (measurable_const.inner measurable_fst)
    · exact measurable_const
  have hsub : {q : E d × Bool | ∃ x' ∈ lpBall p q.1 ε, linClf w x' ≠ q.2} ⊆ T := by
    rintro ⟨x, y⟩ ⟨x', hx', hne⟩
    simp only [lpBall, Set.mem_ofPred_eq] at hx'
    have k1 : inner ℝ w (x' - x) ≤ L := l20_key p hp ε hε w _ hx'
    have k2 : inner ℝ w (x - x') ≤ L := by
      refine l20_key p hp ε hε w _ ?_
      rw [← neg_sub, l20_lp_neg p hp]; exact hx'
    rw [inner_sub_right] at k1 k2
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
  set s : ℝ := (inner ℝ w θ - L) / σ with hs
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hσ.le
  have hsσ : σ * s = inner ℝ w θ - L := by rw [hs]; field_simp
  have he : (s * ‖w‖) ^ 2 / (2 * ‖w‖ ^ 2) = (inner ℝ w θ - L) ^ 2 / (2 * σ ^ 2) := by
    rw [hw, hs]; field_simp
  have hA : stdGaussian (E d) {v | lab true * inner ℝ w (θ + σ • v) ≤ L}
      ≤ ENNReal.ofReal (Real.exp (-((inner ℝ w θ - L) ^ 2 / (2 * σ ^ 2)))) := by
    have hc := l20_chern (-w) (neg_ne_zero.2 hwne) (s * ‖w‖) (by positivity)
    rw [norm_neg, he] at hc
    refine le_trans (measure_mono ?_) hc
    intro v hv
    simp only [Set.mem_ofPred_eq, lab, one_mul, inner_add_right, inner_smul_right] at hv ⊢
    rw [inner_neg_left, hw, mul_one]
    have h2 : σ * s ≤ σ * (-inner ℝ w v) := by nlinarith
    exact le_of_mul_le_mul_left h2 hσ
  have hB : stdGaussian (E d) {v | lab false * inner ℝ w (-θ + σ • v) ≤ L}
      ≤ ENNReal.ofReal (Real.exp (-((inner ℝ w θ - L) ^ 2 / (2 * σ ^ 2)))) := by
    have hc := l20_chern w hwne (s * ‖w‖) (by positivity)
    rw [he] at hc
    refine le_trans (measure_mono ?_) hc
    intro v hv
    simp only [Set.mem_ofPred_eq, lab, inner_add_right, inner_smul_right, inner_neg_right] at hv ⊢
    rw [hw, mul_one]
    have h2 : σ * s ≤ σ * (inner ℝ w v) := by nlinarith
    exact le_of_mul_le_mul_left h2 hσ
  have hfin : -(inner ℝ w θ - L) ^ 2 / (2 * σ ^ 2) = -((inner ℝ w θ - L) ^ 2 / (2 * σ ^ 2)) :=
    neg_div _ _
  rw [hfin]
  calc robustErrP p (gaussModel θ σ) (linClf w) ε ≤ gaussModel θ σ T := measure_mono hsub
    _ = _ := hG
    _ ≤ (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-((inner ℝ w θ - L) ^ 2 / (2 * σ ^ 2))))
          + (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-((inner ℝ w θ - L) ^ 2 / (2 * σ ^ 2)))) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (-((inner ℝ w θ - L) ^ 2 / (2 * σ ^ 2)))) := by
        rw [← add_mul, ENNReal.add_halves, one_mul]
