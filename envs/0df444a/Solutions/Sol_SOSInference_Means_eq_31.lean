-- Prove2me | solution 1 for SOSInference.Means.eq_31
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T06:13:40.696143+00:00
-- url     : https://prove2.me/submissions/5ada2d6b-4359-45a6-b7ee-bc2153be4660

import Mathlib
import Definitions.Def_SOSInference_Means_tauLaw

open SOSInference.Means
open MeasureTheory ProbabilityTheory

namespace SOSRhoAux

variable {l : ℕ} (M : Model l) (hM : M.Standing)

include hM in
lemma lawX_prob : IsProbabilityMeasure (lawX M) := by
  constructor
  simp only [lawX, lawOfDensity]
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hM.lintegral_fX]

include hM in
lemma Lam_pos (x : E l) : 0 < Lam M x 0 := by
  unfold Lam
  have h1 := hM.fX_pos (x + (1 / 2 : ℝ) • (0 : E l))
  have h2 := hM.fY_pos (x + (1 / 2 : ℝ) • (0 : E l))
  have h3 := hM.kappa_nonneg
  have hG : 0 < Real.Gamma ((l : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hpi : 0 < Real.pi ^ ((l : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have : 0 < M.fX (x + (1 / 2 : ℝ) • (0 : E l)) + M.κ * M.fY (x + (1 / 2 : ℝ) • (0 : E l)) := by
    nlinarith
  positivity

include hM in
lemma Lam_meas : Measurable (fun x => Lam M x 0) := by
  unfold Lam
  have h1 : Measurable (fun x : E l => M.fX (x + (1 / 2 : ℝ) • (0 : E l))) :=
    hM.measurable_fX.comp (measurable_id.add_const _)
  have h2 : Measurable (fun x : E l => M.fY (x + (1 / 2 : ℝ) • (0 : E l))) :=
    hM.measurable_fY.comp (measurable_id.add_const _)
  exact ((h1.add (h2.const_mul _)).mul_const _).div_const _

lemma expMeasure_meas {f : E l → ℝ} (hf : Measurable f) :
    Measurable (fun x => expMeasure (f x)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [expMeasure, gammaMeasure]
  simp_rw [withDensity_apply _ hs]
  have : Measurable (fun p : E l × ℝ => gammaPDF 1 (f p.1) p.2) := by
    unfold gammaPDF gammaPDFReal
    apply Measurable.ennreal_ofReal
    apply Measurable.ite (measurableSet_le measurable_const measurable_snd)
    · fun_prop
    · exact measurable_const
  exact this.lintegral_prod_right'

include hM in
/-- The CDF of `τ(0)` as an integral. -/
lemma tauLaw_Iic (t : ℝ) (ht : 0 ≤ t) :
    tauLaw M 0 (Set.Iic t) = ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-(Lam M x 0 * t))) ∂(lawX M) := by
  unfold tauLaw
  rw [Measure.bind_apply measurableSet_Iic (expMeasure_meas (Lam_meas M hM)).aemeasurable]
  apply lintegral_congr
  intro x
  have hr := Lam_pos M hM x
  haveI := isProbabilityMeasure_expMeasure hr
  have h := cdf_expMeasure_eq hr t
  rw [cdf_eq_real, if_pos ht] at h
  rw [← h, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- `H(t) = E[1 - exp(-Λ(X,0) t)]`. -/
noncomputable def H (t : ℝ) : ℝ := ∫ x, (1 - Real.exp (-(Lam M x 0 * t))) ∂(lawX M)

include hM in
lemma gtilde_eq (y : E l) : gtilde M y = H M (‖y‖ ^ 2) := by
  unfold gtilde H
  rw [tauLaw_Iic M hM _ (by positivity)]
  haveI := lawX_prob M hM
  rw [integral_eq_lintegral_of_nonneg_ae]
  · exact Filter.Eventually.of_forall fun x => by
      have := Lam_pos M hM x
      simp only [Pi.zero_apply, sub_nonneg, Real.exp_le_one_iff, Left.neg_nonpos_iff]
      positivity
  · exact ((Lam_meas M hM).mul_const _).neg.exp.const_sub _ |>.aestronglyMeasurable

include hM in
lemma integrable_term (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x => 1 - Real.exp (-(Lam M x 0 * t))) (lawX M) := by
  haveI := lawX_prob M hM
  refine Integrable.of_bound
    (((Lam_meas M hM).mul_const _).neg.exp.const_sub _).aestronglyMeasurable 1 ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have := Lam_pos M hM x
  have h1 : Real.exp (-(Lam M x 0 * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have h2 := Real.exp_pos (-(Lam M x 0 * t))
  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith

include hM in
lemma H_le_one (t : ℝ) (ht : 0 ≤ t) : H M t ≤ 1 := by
  haveI := lawX_prob M hM
  unfold H
  calc ∫ x, (1 - Real.exp (-(Lam M x 0 * t))) ∂(lawX M) ≤ ∫ x, (1 : ℝ) ∂(lawX M) := by
        apply integral_mono (integrable_term M hM t ht) (integrable_const _)
        intro x; have := Real.exp_pos (-(Lam M x 0 * t)); simp only; linarith
    _ = 1 := by simp

include hM in
lemma H_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : H M s ≤ H M t := by
  unfold H
  apply integral_mono (integrable_term M hM s hs) (integrable_term M hM t (hs.trans hst))
  intro x
  have := Lam_pos M hM x
  simp only
  have : Real.exp (-(Lam M x 0 * t)) ≤ Real.exp (-(Lam M x 0 * s)) := by
    apply Real.exp_le_exp.mpr; nlinarith
  linarith

include hM in
lemma H_pos {t : ℝ} (ht : 0 < t) : 0 < H M t := by
  haveI := lawX_prob M hM
  unfold H
  rw [integral_pos_iff_support_of_nonneg _ (integrable_term M hM t ht.le)]
  · have : Function.support (fun x => 1 - Real.exp (-(Lam M x 0 * t))) = Set.univ := by
      ext x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      have := Lam_pos M hM x
      have : Real.exp (-(Lam M x 0 * t)) < 1 := by
        have h0 := Real.exp_lt_exp.mpr (show -(Lam M x 0 * t) < 0 by nlinarith)
        simpa using h0
      linarith
    rw [this]; simp
  · intro x
    have := Lam_pos M hM x
    simp only [Pi.zero_apply, sub_nonneg, Real.exp_le_one_iff, Left.neg_nonpos_iff]
    positivity

include hM in
lemma H_cont (c : ℝ) (hc : 0 ≤ c) : Continuous (fun r : ℝ => H M (r ^ 2 * c)) := by
  haveI := lawX_prob M hM
  unfold H
  apply continuous_of_dominated (bound := fun _ => 1)
  · intro r
    exact (((Lam_meas M hM).mul_const _).neg.exp.const_sub _).aestronglyMeasurable
  · intro r
    refine Filter.Eventually.of_forall fun x => ?_
    have := Lam_pos M hM x
    have hrc : 0 ≤ r ^ 2 * c := by positivity
    have h1 : Real.exp (-(Lam M x 0 * (r ^ 2 * c))) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have h2 := Real.exp_pos (-(Lam M x 0 * (r ^ 2 * c)))
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun x => by fun_prop

end SOSRhoAux

open SOSRhoAux in
theorem solution (M : Model 2) (hM : M.Standing) (z : E 2) (hz : z ≠ 0) :
    (∃! r : ℝ, 0 < r ∧ 1 / r = gtilde M (r • z)) ∧
      0 < rho M z ∧ 1 / rho M z = gtilde M (rho M z • z) := by
  set c := ‖z‖ ^ 2 with hc
  have hc0 : 0 < c := by have := norm_pos_iff.mpr hz; positivity
  have hg : ∀ r : ℝ, gtilde M (r • z) = H M (r ^ 2 * c) := by
    intro r
    rw [gtilde_eq M hM, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  -- the function φ(r) = r H(r² c)
  have hHpos : ∀ r : ℝ, r ≠ 0 → 0 < H M (r ^ 2 * c) := fun r hr =>
    H_pos M hM (by positivity)
  have hHmono : ∀ r s : ℝ, 0 ≤ r → r ≤ s → H M (r ^ 2 * c) ≤ H M (s ^ 2 * c) := by
    intro r s hr hrs
    apply H_mono M hM (by positivity)
    have : r ^ 2 ≤ s ^ 2 := by nlinarith
    nlinarith
  have hiff : ∀ r : ℝ, 0 < r → (1 / r = gtilde M (r • z) ↔ r * H M (r ^ 2 * c) = 1) := by
    intro r hr
    rw [hg r]
    constructor
    · intro h; rw [← h]; field_simp
    · intro h; field_simp; linarith
  -- existence by the intermediate value theorem
  set h1 := H M (1 ^ 2 * c) with hh1
  have h1pos : 0 < h1 := hHpos 1 one_ne_zero
  have h1le : h1 ≤ 1 := H_le_one M hM _ (by positivity)
  set b := 1 / h1 with hb
  have hb1 : 1 ≤ b := by rw [hb, le_div_iff₀ h1pos]; linarith
  have hcont : Continuous (fun r : ℝ => r * H M (r ^ 2 * c)) :=
    continuous_id.mul (H_cont M hM c hc0.le)
  have hivt := intermediate_value_Icc hb1 hcont.continuousOn
  have hmem : (1 : ℝ) ∈ Set.Icc ((fun r : ℝ => r * H M (r ^ 2 * c)) 1)
      ((fun r : ℝ => r * H M (r ^ 2 * c)) b) := by
    constructor
    · simp only [one_mul]; exact h1le
    · simp only
      have := hHmono 1 b zero_le_one hb1
      have hbh : b * h1 = 1 := by rw [hb]; field_simp
      nlinarith
  obtain ⟨r0, ⟨hr0a, -⟩, hr0⟩ := hivt hmem
  have hr0pos : 0 < r0 := lt_of_lt_of_le one_pos hr0a
  -- uniqueness
  have huniq : ∀ r : ℝ, 0 < r ∧ 1 / r = gtilde M (r • z) → r = r0 := by
    rintro r ⟨hr, hreq⟩
    have e1 := (hiff r hr).mp hreq
    have e0 : r0 * H M (r0 ^ 2 * c) = 1 := hr0
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hHmono r r0 hr.le hlt.le
      have := hHpos r hr.ne'
      nlinarith
    · have := hHmono r0 r hr0pos.le hlt.le
      have := hHpos r0 hr0pos.ne'
      nlinarith
  have hr0sol : 0 < r0 ∧ 1 / r0 = gtilde M (r0 • z) := ⟨hr0pos, (hiff r0 hr0pos).mpr hr0⟩
  have hrho : rho M z = r0 := by
    unfold rho
    rw [if_neg hz]
    have : {r : ℝ | 0 < r ∧ 1 / r = gtilde M (r • z)} = {r0} := by
      ext r; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨huniq r, fun h => h ▸ hr0sol⟩
    rw [this, csInf_singleton]
  refine ⟨⟨r0, hr0sol, huniq⟩, ?_⟩
  rw [hrho]; exact hr0sol
