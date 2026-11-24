-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.theorem_5_12
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-24T01:35:14.620308+00:00
-- url     : https://prove2.me/submissions/7ec28116-8e02-4fd7-8294-84c730b78ae4

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Supplement_QExLearner
import Theorems.Thm_QuantumLTF_Membership_lemma_2_1

namespace Aux_wqexlb

open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Membership.Supplement

/-! ### Part 1: Gaussian L² Density and Quantum Example State Inner Products -/

noncomputable def gaussDens (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2)

lemma gaussDens_nonneg (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ gaussDens n x := by
  unfold gaussDens
  positivity

lemma gaussDens_measurable (n : ℕ) : Measurable (gaussDens n) := by
  unfold gaussDens
  fun_prop

lemma gaussDens_toLp_eq_prod (n : ℕ) (y : Fin n → ℝ) :
    gaussDens n (WithLp.toLp 2 y) = ∏ i : Fin n, gaussianPDFReal 0 1 (y i) := by
  unfold gaussDens gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Real.exp_sum]
  congr 1
  · rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity),
      ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  · congr 1
    rw [PiLp.norm_sq_eq_of_L2]
    have h_term : ∀ i : Fin n, ‖WithLp.toLp 2 y i‖ ^ 2 = y i ^ 2 := fun i => by
      change ‖y i‖ ^ 2 = y i ^ 2
      rw [Real.norm_eq_abs, sq_abs]
    simp_rw [h_term, ← Finset.sum_div, ← Finset.sum_neg_distrib]

lemma pi_gaussianReal_eq_withDensity (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun y => ENNReal.ofReal (∏ i : Fin n, gaussianPDFReal 0 1 (y i))) := by
  refine Measure.pi_eq (fun s hs => ?_)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  let f : Fin n → ℝ → ℝ := fun i t => (s i).indicator (gaussianPDFReal 0 1) t
  have hf_int : ∀ i, Integrable (f i) volume :=
    fun i => (integrable_gaussianPDFReal 0 1).indicator (hs i)
  have hprod_int : Integrable (fun y : Fin n → ℝ => ∏ i, f i (y i)) volume :=
    Integrable.fintype_prod hf_int
  have hprod_eq : ∀ y : Fin n → ℝ, (∏ i, f i (y i)) =
      (Set.univ.pi s).indicator (fun y => ∏ i, gaussianPDFReal 0 1 (y i)) y := by
    intro y
    by_cases hy : y ∈ Set.univ.pi s
    · simp only [Set.mem_pi, Set.mem_univ, forall_true_left] at hy
      rw [Set.indicator_of_mem (by simpa using hy)]
      refine Finset.prod_congr rfl fun i _ => Set.indicator_of_mem (hy i) _
    · rw [Set.indicator_of_notMem hy]
      simp only [Set.mem_pi, Set.mem_univ, forall_true_left, not_forall] at hy
      obtain ⟨i, hi⟩ := hy
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
  have hprod_nonneg : 0 ≤ (fun y : Fin n → ℝ => ∏ i, f i (y i)) := fun y =>
    Finset.prod_nonneg fun i _ => Set.indicator_nonneg (fun t _ => gaussianPDFReal_nonneg 0 1 t) _
  have h_lint : ∫⁻ y in Set.univ.pi s, ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (y i)) ∂volume =
      ENNReal.ofReal (∫ y : Fin n → ℝ, ∏ i, f i (y i) ∂volume) := by
    rw [ofReal_integral_eq_lintegral_ofReal hprod_int (ae_of_all _ hprod_nonneg)]
    rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
    refine lintegral_congr fun y => ?_
    rw [hprod_eq y]
    by_cases hy : y ∈ Set.univ.pi s <;> simp [hy]
  rw [h_lint, integral_fintype_prod_volume_eq_prod]
  have h_fac_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ ∫ t, f i t ∂volume := fun i _ =>
    integral_nonneg (fun t => Set.indicator_nonneg (fun _ _ => gaussianPDFReal_nonneg 0 1 _) t)
  rw [ENNReal.ofReal_prod_of_nonneg h_fac_nonneg]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero (s i)]
  simp only [f, integral_indicator (hs i)]

lemma stdGaussian_eq_withDensity (n : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin n)) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (fun x => ENNReal.ofReal (gaussDens n x)) := by
  rw [← map_pi_eq_stdGaussian, pi_gaussianReal_eq_withDensity]
  let e : (Fin n → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin n) :=
    { toEquiv := (WithLp.equiv 2 (Fin n → ℝ)).symm
      measurable_toFun := (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).measurable
      measurable_invFun := (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)).measurable }
  have he_coe : (e : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) = WithLp.toLp 2 := rfl
  have hmp : MeasurePreserving e volume volume := PiLp.volume_preserving_toLp (Fin n)
  ext s hs
  rw [← he_coe, e.map_apply, withDensity_apply _ (e.measurable hs), withDensity_apply _ hs]
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin n))) = Measure.map e volume := hmp.map_eq.symm
  rw [hvol, setLIntegral_map hs ((gaussDens_measurable n).ennreal_ofReal) e.measurable]
  refine lintegral_congr fun y => ?_
  simp [he_coe, gaussDens_toLp_eq_prod]

lemma measurable_ltf_zero {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    Measurable (ltf w 0) := by
  unfold ltf sgn
  refine Measurable.ite (measurableSet_le measurable_const (by fun_prop)) measurable_const measurable_const

lemma measurableSet_cond {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    MeasurableSet {p : EuclideanSpace ℝ (Fin n) × Bool | p.2 = decide (ltf w 0 p.1 = -1)} := by
  have h1 : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | ltf w 0 x = -1} :=
    (measurable_ltf_zero w) (measurableSet_singleton (-1))
  have h_eq : {p : EuclideanSpace ℝ (Fin n) × Bool | p.2 = decide (ltf w 0 p.1 = -1)} =
      ({x | ltf w 0 x = -1} ×ˢ {true}) ∪ ({x | ltf w 0 x = -1}ᶜ ×ˢ {false}) := by
    ext ⟨x, b⟩
    cases b <;> simp [eq_comm]
  rw [h_eq]
  exact (h1.prod (measurableSet_singleton true)).union (h1.compl.prod (measurableSet_singleton false))

lemma measurable_gaussExampleState {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    Measurable (gaussExampleState w) := by
  unfold gaussExampleState
  refine Measurable.ite (measurableSet_cond w) ?_ measurable_const
  have : Measurable (fun p : EuclideanSpace ℝ (Fin n) × Bool => Real.sqrt (gaussDens n p.1)) :=
    ((gaussDens_measurable n).comp measurable_fst).sqrt
  exact Complex.measurable_ofReal.comp this

lemma gaussExampleState_memLp {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    MemLp (gaussExampleState w) 2
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod (Measure.count : Measure Bool)) := by
  refine ⟨(measurable_gaussExampleState w).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  have h_eq : ∀ p : EuclideanSpace ℝ (Fin n) × Bool,
      ‖gaussExampleState w p‖ₑ ^ (2 : ℝ) =
        if p.2 = decide (ltf w 0 p.1 = -1) then ENNReal.ofReal (gaussDens n p.1) else 0 := by
    intro ⟨x, b⟩
    unfold gaussExampleState
    split_ifs
    · have hnn : 0 ≤ Real.sqrt (gaussDens n x) := Real.sqrt_nonneg _
      have hsub : (2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2) = gaussDens n x := rfl
      rw [hsub, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hnn]
      rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow hnn, Real.sq_sqrt (gaussDens_nonneg n x)]
    · rw [enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
  simp_rw [h_eq]
  rw [lintegral_prod]
  · simp_rw [lintegral_count, tsum_fintype, Fintype.sum_bool]
    have h_sum : ∀ x,
        (if true = decide (ltf w 0 x = -1) then ENNReal.ofReal (gaussDens n x) else 0) +
        (if false = decide (ltf w 0 x = -1) then ENNReal.ofReal (gaussDens n x) else 0) =
          ENNReal.ofReal (gaussDens n x) := by
      intro x
      rcases Bool.dichotomy (decide (ltf w 0 x = -1)) with h | h <;> rw [h] <;> simp
    simp_rw [h_sum]
    have h_tot : ∫⁻ x, ENNReal.ofReal (gaussDens n x) ∂volume = 1 := by
      have := congrArg (fun m : Measure (EuclideanSpace ℝ (Fin n)) => m Set.univ)
        (stdGaussian_eq_withDensity n)
      rw [measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
      exact this.symm
    rw [h_tot]
    exact ENNReal.one_lt_top
  · refine Measurable.aemeasurable ?_
    exact Measurable.ite (measurableSet_cond w)
      ((gaussDens_measurable n).comp measurable_fst |>.ennreal_ofReal) measurable_const

noncomputable def exVec {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) : ExSpace n :=
  (gaussExampleState_memLp w).toLp (gaussExampleState w)

lemma exVec_inner {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    inner ℂ (exVec u) (exVec v) = ((1 - disagree (ltf u 0) (ltf v 0) : ℝ) : ℂ) := by
  rw [L2.inner_def]
  let μP : Measure (EuclideanSpace ℝ (Fin n) × Bool) :=
    (volume : Measure (EuclideanSpace ℝ (Fin n))).prod (Measure.count : Measure Bool)
  have hu_ae : (exVec u : EuclideanSpace ℝ (Fin n) × Bool → ℂ) =ᵐ[μP] gaussExampleState u :=
    (gaussExampleState_memLp u).coeFn_toLp
  have hv_ae : (exVec v : EuclideanSpace ℝ (Fin n) × Bool → ℂ) =ᵐ[μP] gaussExampleState v :=
    (gaussExampleState_memLp v).coeFn_toLp
  have h_ae : (fun p => inner ℂ ((exVec u) p) ((exVec v) p)) =ᵐ[μP]
      (fun p => inner ℂ (gaussExampleState u p) (gaussExampleState v p)) := by
    filter_upwards [hu_ae, hv_ae] with p h1 h2
    rw [h1, h2]
  rw [integral_congr_ae h_ae]
  have h_pt : ∀ p : EuclideanSpace ℝ (Fin n) × Bool,
      inner ℂ (gaussExampleState u p) (gaussExampleState v p) =
        ((if p.2 = decide (ltf u 0 p.1 = -1) ∧ p.2 = decide (ltf v 0 p.1 = -1) then
          gaussDens n p.1 else 0 : ℝ) : ℂ) := by
    intro ⟨x, b⟩
    have hsub : (2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2) = gaussDens n x := rfl
    by_cases h1 : b = decide (ltf u 0 x = -1) <;> by_cases h2 : b = decide (ltf v 0 x = -1)
    · rw [if_pos ⟨h1, h2⟩]
      unfold gaussExampleState
      dsimp only
      rw [if_pos h1, if_pos h2, hsub, RCLike.inner_apply, Complex.conj_ofReal,
        ← Complex.ofReal_mul, Real.mul_self_sqrt (gaussDens_nonneg n x)]
    · rw [if_neg (fun hc => h2 hc.2)]
      unfold gaussExampleState
      dsimp only
      rw [if_pos h1, if_neg h2]
      simp
    · rw [if_neg (fun hc => h1 hc.1)]
      unfold gaussExampleState
      dsimp only
      rw [if_neg h1, if_pos h2]
      simp
    · rw [if_neg (fun hc => h1 hc.1)]
      unfold gaussExampleState
      dsimp only
      rw [if_neg h1, if_neg h2]
      simp
  simp_rw [h_pt]
  have h_int_real : Integrable (fun p : EuclideanSpace ℝ (Fin n) × Bool =>
      if p.2 = decide (ltf u 0 p.1 = -1) ∧ p.2 = decide (ltf v 0 p.1 = -1) then
        gaussDens n p.1 else 0) μP := by
    have h_mul : Integrable (fun p : EuclideanSpace ℝ (Fin n) × Bool =>
        ‖gaussExampleState u p * gaussExampleState v p‖) μP :=
      ((gaussExampleState_memLp u).integrable_mul (gaussExampleState_memLp v)).norm
    refine h_mul.mono' ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      refine Measurable.ite ?_ ((gaussDens_measurable n).comp measurable_fst) measurable_const
      exact (measurableSet_cond u).inter (measurableSet_cond v)
    · filter_upwards with ⟨x, b⟩
      by_cases h : b = decide (ltf u 0 x = -1) ∧ b = decide (ltf v 0 x = -1)
      · rw [if_pos h, Real.norm_of_nonneg (gaussDens_nonneg n x), norm_mul]
        have hsub : (2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2) = gaussDens n x := rfl
        unfold gaussExampleState
        dsimp only
        rw [if_pos h.1, if_pos h.2, hsub, Complex.norm_real,
          Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.mul_self_sqrt (gaussDens_nonneg n x)]
      · rw [if_neg h, norm_zero]
        exact norm_nonneg _
  change (∫ p, (((if p.2 = decide (ltf u 0 p.1 = -1) ∧ p.2 = decide (ltf v 0 p.1 = -1) then
        gaussDens n p.1 else 0 : ℝ) : ℂ)) ∂μP) = _
  rw [integral_complex_ofReal]
  congr 1
  rw [integral_prod _ h_int_real]
  simp_rw [integral_count, Fintype.sum_bool]
  have h_sum_x : ∀ x : EuclideanSpace ℝ (Fin n),
      (if true = decide (ltf u 0 x = -1) ∧ true = decide (ltf v 0 x = -1) then gaussDens n x else 0) +
      (if false = decide (ltf u 0 x = -1) ∧ false = decide (ltf v 0 x = -1) then gaussDens n x else 0) =
        {x' | ltf u 0 x' = ltf v 0 x'}.indicator (gaussDens n) x := by
    intro x
    have hu : ltf u 0 x = 1 ∨ ltf u 0 x = -1 := by unfold ltf sgn; split_ifs <;> simp
    have hv : ltf v 0 x = 1 ∨ ltf v 0 x = -1 := by unfold ltf sgn; split_ifs <;> simp
    rcases hu with hu | hu <;> rcases hv with hv | hv <;> simp [hu, hv, Set.indicator]
  simp_rw [h_sum_x]
  let S : Set (EuclideanSpace ℝ (Fin n)) := {x | ltf u 0 x = ltf v 0 x}
  have hS : MeasurableSet S := measurableSet_eq_fun (measurable_ltf_zero u) (measurable_ltf_zero v)
  have h_std : (stdGaussian (EuclideanSpace ℝ (Fin n)) S).toReal =
      ∫ x, S.indicator (gaussDens n) x ∂volume := by
    rw [stdGaussian_eq_withDensity, withDensity_apply _ hS]
    have h_int_dens : Integrable (gaussDens n) volume := by
      rw [← memLp_one_iff_integrable]
      refine ⟨(gaussDens_measurable n).aestronglyMeasurable, ?_⟩
      rw [eLpNorm_one_eq_lintegral_enorm]
      have h_eq_en : ∀ x, ‖gaussDens n x‖ₑ = ENNReal.ofReal (gaussDens n x) := fun x => by
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (gaussDens_nonneg n x)]
      simp_rw [h_eq_en]
      have h1 := congrArg (fun m : Measure (EuclideanSpace ℝ (Fin n)) => m Set.univ)
        (stdGaussian_eq_withDensity n)
      rw [measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
      rw [← h1]
      exact ENNReal.one_lt_top
    rw [← ofReal_integral_eq_lintegral_ofReal h_int_dens.restrict (ae_of_all _ (gaussDens_nonneg n))]
    rw [ENNReal.toReal_ofReal (setIntegral_nonneg hS (fun x _ => gaussDens_nonneg n x))]
    exact (integral_indicator hS).symm
  rw [← h_std]
  unfold disagree
  have hS_compl : Sᶜ = {x | ltf u 0 x ≠ ltf v 0 x} := rfl
  rw [← hS_compl, measure_compl hS (measure_ne_top _ _), measure_univ]
  have hle1 : stdGaussian (EuclideanSpace ℝ (Fin n)) S ≤ 1 :=
    (measure_mono (Set.subset_univ S)).trans_eq measure_univ
  rw [ENNReal.toReal_sub_of_le hle1 (by simp), ENNReal.toReal_one]
  ring

lemma exVec_norm {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) : ‖exVec w‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow]
  have h : (‖exVec w‖ ^ 2 : ℝ) = RCLike.re (inner ℂ (exVec w) (exVec w)) := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rw [h, exVec_inner]
  have hd : disagree (ltf w 0) (ltf w 0) = 0 := by
    unfold disagree
    simp
  simp [hd]

lemma exVec_norm_sub_sq {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    ‖exVec u - exVec v‖ ^ 2 = 2 * disagree (ltf u 0) (ltf v 0) := by
  rw [norm_sub_sq (𝕜 := ℂ) (exVec u) (exVec v), exVec_norm, exVec_norm, exVec_inner]
  simp only [RCLike.re_to_complex, Complex.ofReal_re]
  ring

/-! ### Part 2: Two-Step Householder Oracle Construction -/

section Householder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

noncomputable def householderFun (v : H) (f : H) : H :=
  ((2 / (‖v‖ ^ 2 : ℝ) : ℝ) : ℂ) • (inner ℂ v f • v) - f

lemma householderFun_invol {v : H} (hv : v ≠ 0) (f : H) :
    householderFun v (householderFun v f) = f := by
  unfold householderFun
  have h_in : inner ℂ v (((2 / ‖v‖ ^ 2 : ℝ) : ℂ) • (inner ℂ v f • v) - f) = inner ℂ v f := by
    rw [inner_sub_right, inner_smul_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp only [Complex.coe_algebraMap]
    push_cast
    have hv_c : (‖v‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv)
    field_simp [hv_c]
    ring
  rw [h_in]
  abel

lemma householderFun_norm {v : H} (hv : v ≠ 0) (f : H) :
    ‖householderFun v f‖ = ‖f‖ := by
  have hv2 : (‖v‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  unfold householderFun
  rw [@norm_sub_sq ℂ H]
  have h_t1 : ‖((2 / ‖v‖ ^ 2 : ℝ) : ℂ) • (inner ℂ v f • v)‖ ^ 2 =
      4 / ‖v‖ ^ 2 * ‖inner ℂ v f‖ ^ 2 := by
    rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    field_simp [hv2]
    ring
  have h_t2 : RCLike.re (inner ℂ (((2 / ‖v‖ ^ 2 : ℝ) : ℂ) • (inner ℂ v f • v)) f) =
      2 / ‖v‖ ^ 2 * ‖inner ℂ v f‖ ^ 2 := by
    rw [inner_smul_left, inner_smul_left]
    simp only [Complex.conj_ofReal]
    have h_conj : (starRingEnd ℂ) (inner ℂ v f) * inner ℂ v f = ((‖inner ℂ v f‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [h_conj, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
  rw [h_t1, h_t2]
  ring

noncomputable def householderEquiv {v : H} (hv : v ≠ 0) : H ≃ₗᵢ[ℂ] H where
  toFun := householderFun v
  invFun := householderFun v
  left_inv := householderFun_invol hv
  right_inv := householderFun_invol hv
  map_add' x y := by
    unfold householderFun
    rw [inner_add_right, add_smul, smul_add]
    abel
  map_smul' c x := by
    unfold householderFun
    rw [inner_smul_right, RingHom.id_apply, smul_smul, smul_smul, smul_sub, smul_smul]
    congr 1
    ring_nf
  norm_map' := householderFun_norm hv

lemma householderEquiv_apply_of_real_inner {x y : H} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (him : (inner ℂ x y).im = 0) (hre : 0 ≤ (inner ℂ x y).re) :
    ∃ hv : x + y ≠ 0, householderEquiv hv x = y := by
  have h_sq : ‖x + y‖ ^ 2 = 2 * (1 + (inner ℂ x y).re) := by
    rw [@norm_add_sq ℂ H, hx, hy]
    simp only [RCLike.re_to_complex]
    ring
  have hv_pos : 2 ≤ ‖x + y‖ ^ 2 := by linarith
  have hv : x + y ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv_pos
    norm_num at hv_pos
  refine ⟨hv, ?_⟩
  change householderFun (x + y) x = y
  unfold householderFun
  have h_in : inner ℂ (x + y) x = ((1 + (inner ℂ x y).re : ℝ) : ℂ) := by
    rw [inner_add_left, inner_self_eq_norm_sq_to_K, hx]
    have hyx : inner ℂ y x = inner ℂ x y := by
      rw [← inner_conj_symm y x, Complex.conj_eq_iff_im.mpr him]
    rw [hyx, Complex.ext_iff]
    simp [him]
  rw [h_in, h_sq, smul_smul]
  have h1 : ((2 / (2 * (1 + (inner ℂ x y).re)) : ℝ) : ℂ) * ((1 + (inner ℂ x y).re : ℝ) : ℂ) = 1 := by
    have hden_r : (1 + (inner ℂ x y).re : ℝ) ≠ 0 := by linarith
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp [hden_r]
  rw [h1, one_smul]
  abel

lemma unit_phase_householder (a b : H) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ∃ V : H ≃ₗᵢ[ℂ] H, V a = b := by
  let c : ℂ := inner ℂ a b
  let ζ : ℂ := if c = 0 then 1 else c / (‖c‖ : ℂ)
  have hζ_norm : ‖ζ‖ = 1 := by
    by_cases hc : c = 0
    · simp [ζ, hc]
    · simp only [ζ, if_neg hc, norm_div, Complex.norm_real, norm_norm]
      exact div_self (norm_ne_zero_iff.mpr hc)
  let Φ : H ≃ₗᵢ[ℂ] H :=
    { toFun := fun f => ζ • f
      invFun := fun f => ζ⁻¹ • f
      left_inv := fun f => by
        dsimp only
        rw [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mp (by rw [hζ_norm]; norm_num)), one_smul]
      right_inv := fun f => by
        dsimp only
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mp (by rw [hζ_norm]; norm_num)), one_smul]
      map_add' := fun x y => smul_add ζ x y
      map_smul' := fun r x => smul_comm ζ r x
      norm_map' := fun f => by
        change ‖ζ • f‖ = ‖f‖
        rw [norm_smul, hζ_norm, one_mul] }
  have hΦa : ‖Φ a‖ = 1 := by rw [Φ.norm_map, ha]
  have h_inner : inner ℂ (Φ a) b = ((‖c‖ : ℝ) : ℂ) := by
    change inner ℂ (ζ • a) b = _
    rw [inner_smul_left]
    by_cases hc : c = 0
    · simp [ζ, hc, c]
    · simp only [ζ, if_neg hc, map_div₀, Complex.conj_ofReal]
      have hmul : (starRingEnd ℂ) c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [div_mul_eq_mul_div, show (starRingEnd ℂ) c * inner ℂ a b = (starRingEnd ℂ) c * c from rfl, hmul]
      have hn : (‖c‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hc)
      push_cast
      field_simp [hn]
  have him : (inner ℂ (Φ a) b).im = 0 := by rw [h_inner]; simp
  have hre : 0 ≤ (inner ℂ (Φ a) b).re := by rw [h_inner]; simp [norm_nonneg]
  obtain ⟨hv, hR⟩ := householderEquiv_apply_of_real_inner hΦa hb him hre
  exact ⟨Φ.trans (householderEquiv hv), by simpa using hR⟩

lemma norm_unitize_sub_le {a b : H} (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖((‖a‖⁻¹ : ℝ) : ℂ) • a - ((‖b‖⁻¹ : ℝ) : ℂ) • b‖ ≤ 2 * ‖a - b‖ / ‖a‖ := by
  have ha_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hb_pos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have h_eq : ((‖a‖⁻¹ : ℝ) : ℂ) • a - ((‖b‖⁻¹ : ℝ) : ℂ) • b =
      ((‖a‖⁻¹ : ℝ) : ℂ) • (a - b) + (((‖a‖⁻¹ - ‖b‖⁻¹ : ℝ) : ℂ)) • b := by
    rw [smul_sub, Complex.ofReal_sub, sub_smul]
    abel
  rw [h_eq]
  calc ‖((‖a‖⁻¹ : ℝ) : ℂ) • (a - b) + (((‖a‖⁻¹ - ‖b‖⁻¹ : ℝ) : ℂ)) • b‖
      ≤ ‖((‖a‖⁻¹ : ℝ) : ℂ) • (a - b)‖ + ‖(((‖a‖⁻¹ - ‖b‖⁻¹ : ℝ) : ℂ)) • b‖ := norm_add_le _ _
    _ = ‖a‖⁻¹ * ‖a - b‖ + |‖a‖⁻¹ - ‖b‖⁻¹| * ‖b‖ := by
        rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg (inv_nonneg.mpr ha_pos.le), Real.norm_eq_abs]
    _ = ‖a‖⁻¹ * ‖a - b‖ + |‖b‖ - ‖a‖| / ‖a‖ := by
        congr 1
        have h1 : ‖a‖⁻¹ - ‖b‖⁻¹ = (‖b‖ - ‖a‖) / (‖a‖ * ‖b‖) := by field_simp [ha_pos.ne', hb_pos.ne']
        rw [h1, abs_div, abs_of_pos (mul_pos ha_pos hb_pos)]
        field_simp [ha_pos.ne', hb_pos.ne']
    _ ≤ ‖a‖⁻¹ * ‖a - b‖ + ‖a - b‖ / ‖a‖ := by
        gcongr
        rw [abs_sub_comm]
        exact abs_norm_sub_norm_le a b
    _ = 2 * ‖a - b‖ / ‖a‖ := by ring

lemma householderEquiv_sub_norm_le {φ ψ₁ ψ₂ : H} (hφ : ‖φ‖ = 1) (h1 : ‖ψ₁‖ = 1)
    (hre1 : 0 ≤ (inner ℂ φ ψ₁).re)
    (hv1 : φ + ψ₁ ≠ 0) (hv2 : φ + ψ₂ ≠ 0) (f : H) :
    ‖householderEquiv hv1 f - householderEquiv hv2 f‖ ≤ 4 * Real.sqrt 2 * ‖ψ₁ - ψ₂‖ * ‖f‖ := by
  let v₁ := φ + ψ₁
  let v₂ := φ + ψ₂
  let u₁ : H := ((‖v₁‖⁻¹ : ℝ) : ℂ) • v₁
  let u₂ : H := ((‖v₂‖⁻¹ : ℝ) : ℂ) • v₂
  have hu₁ : ‖u₁‖ = 1 := by
    simp [u₁, norm_smul]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv1)
  have hu₂ : ‖u₂‖ = 1 := by
    simp [u₂, norm_smul]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv2)
  have hv₁_ge : Real.sqrt 2 ≤ ‖v₁‖ := by
    rw [← Real.sqrt_sq (norm_nonneg v₁)]
    refine Real.sqrt_le_sqrt ?_
    change 2 ≤ ‖φ + ψ₁‖ ^ 2
    rw [@norm_add_sq ℂ H, hφ, h1]
    simp only [RCLike.re_to_complex]
    linarith
  have hu_diff : ‖u₁ - u₂‖ ≤ Real.sqrt 2 * ‖ψ₁ - ψ₂‖ := by
    calc ‖u₁ - u₂‖ ≤ 2 * ‖v₁ - v₂‖ / ‖v₁‖ := norm_unitize_sub_le hv1 hv2
      _ = 2 * ‖ψ₁ - ψ₂‖ / ‖v₁‖ := by
          have : v₁ - v₂ = ψ₁ - ψ₂ := by dsimp [v₁, v₂]; abel
          rw [this]
      _ ≤ 2 * ‖ψ₁ - ψ₂‖ / Real.sqrt 2 := by gcongr
      _ = Real.sqrt 2 * ‖ψ₁ - ψ₂‖ := by
          have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
          calc 2 * ‖ψ₁ - ψ₂‖ / Real.sqrt 2 = (Real.sqrt 2 * Real.sqrt 2) * ‖ψ₁ - ψ₂‖ / Real.sqrt 2 := by rw [hsq]
            _ = Real.sqrt 2 * ‖ψ₁ - ψ₂‖ := by field_simp
  have h_eq : ∀ {v : H} (hv : v ≠ 0),
      householderEquiv hv f = (2 : ℂ) • (inner ℂ (((‖v‖⁻¹ : ℝ) : ℂ) • v) f • (((‖v‖⁻¹ : ℝ) : ℂ) • v)) - f := by
    intro v hv
    change householderFun v f = _
    unfold householderFun
    rw [inner_smul_left, smul_smul, smul_smul]
    congr 1
    simp only [Complex.conj_ofReal]
    have hvn : (‖v‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv)
    push_cast
    simp only [smul_smul]
    congr 1
    field_simp [hvn]
  rw [h_eq hv1, h_eq hv2]
  change ‖((2 : ℂ) • (inner ℂ u₁ f • u₁) - f) - ((2 : ℂ) • (inner ℂ u₂ f • u₂) - f)‖ ≤ _
  have h_sub : ((2 : ℂ) • (inner ℂ u₁ f • u₁) - f) - ((2 : ℂ) • (inner ℂ u₂ f • u₂) - f) =
      (2 : ℂ) • (inner ℂ (u₁ - u₂) f • u₁ + inner ℂ u₂ f • (u₁ - u₂)) := by
    rw [inner_sub_left, sub_smul, smul_sub, smul_add, smul_sub]
    module
  rw [h_sub, norm_smul, Complex.norm_ofNat]
  calc 2 * ‖inner ℂ (u₁ - u₂) f • u₁ + inner ℂ u₂ f • (u₁ - u₂)‖
      ≤ 2 * (‖inner ℂ (u₁ - u₂) f • u₁‖ + ‖inner ℂ u₂ f • (u₁ - u₂)‖) := by
        gcongr; exact norm_add_le _ _
    _ = 2 * (‖inner ℂ (u₁ - u₂) f‖ * ‖u₁‖ + ‖inner ℂ u₂ f‖ * ‖u₁ - u₂‖) := by
        simp [norm_smul]
    _ ≤ 2 * (‖u₁ - u₂‖ * ‖f‖ * 1 + (1 * ‖f‖) * ‖u₁ - u₂‖) := by
        rw [hu₁]
        gcongr
        · exact norm_inner_le_norm (u₁ - u₂) f
        · rw [← hu₂]; exact norm_inner_le_norm u₂ f
    _ = 4 * ‖u₁ - u₂‖ * ‖f‖ := by ring
    _ ≤ 4 * (Real.sqrt 2 * ‖ψ₁ - ψ₂‖) * ‖f‖ := by gcongr
    _ = 4 * Real.sqrt 2 * ‖ψ₁ - ψ₂‖ * ‖f‖ := by ring

end Householder

/-! ### Part 3: POVM Total Variation Bound -/

section POVM

lemma pos_op_cauchy_schwarz {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E : H →L[ℂ] H) (hE : E.IsPositive) (x y : H) :
    ‖inner ℂ x (E y)‖ ^ 2 ≤ RCLike.re (inner ℂ x (E x)) * RCLike.re (inner ℂ y (E y)) := by
  let b := inner ℂ x (E y)
  let ζ : ℂ := if b = 0 then 1 else star b / (‖b‖ : ℂ)
  have hζ : ‖ζ‖ = 1 := by
    by_cases hb : b = 0
    · simp [ζ, hb]
    · simp [ζ, hb, Complex.norm_real]
  let z := ζ • y
  have h_re_z : RCLike.re (inner ℂ z (E z)) = RCLike.re (inner ℂ y (E y)) := by
    dsimp [z]
    rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc]
    have hmul : (starRingEnd ℂ) ζ * ζ = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]
      simp
    rw [hmul, one_mul]
  have h_re_xz : RCLike.re (inner ℂ x (E z)) = ‖b‖ := by
    dsimp [z]
    rw [map_smul, inner_smul_right]
    by_cases hb : b = 0
    · simp [b] at hb; simp [hb, b]
    · simp only [ζ, if_neg hb, RCLike.star_def]
      have hmul : (starRingEnd ℂ) b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [div_mul_eq_mul_div, show (starRingEnd ℂ) b * inner ℂ x (E y) = (starRingEnd ℂ) b * b from rfl, hmul]
      have hn : (‖b‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hb)
      have : ((‖b‖ ^ 2 : ℝ) : ℂ) / (‖b‖ : ℂ) = (‖b‖ : ℂ) := by push_cast; field_simp [hn]
      rw [this]
      simp
  have h_quad : ∀ t : ℝ, 0 ≤ RCLike.re (inner ℂ x (E x)) + 2 * t * ‖b‖ + t ^ 2 * RCLike.re (inner ℂ y (E y)) := by
    intro t
    have hnn := hE.re_inner_nonneg_right (x + (t : ℂ) • z)
    rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right,
      inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right] at hnn
    have hsym : inner ℂ z (E x) = (starRingEnd ℂ) (inner ℂ x (E z)) := by
      rw [← hE.inner_left_eq_inner_right z x, inner_conj_symm]
    simp only [Complex.conj_ofReal, map_add] at hnn
    have h_inner_zx : (starRingEnd ℂ) ζ * inner ℂ y (E x) = inner ℂ z (E x) := by
      dsimp [z]; rw [inner_smul_left]
    rw [h_inner_zx, hsym] at hnn
    have h_conj_re : RCLike.re ((t : ℂ) * (starRingEnd ℂ) (inner ℂ x (E z))) =
        t * RCLike.re (inner ℂ x (E z)) := by
      simp only [RCLike.re_to_complex, Complex.re_ofReal_mul, Complex.conj_re]
    have h_re_t : RCLike.re ((t : ℂ) * inner ℂ x (E z)) = t * RCLike.re (inner ℂ x (E z)) := by
      simp only [RCLike.re_to_complex, Complex.re_ofReal_mul]
    have h_re_t2 : RCLike.re ((t : ℂ) * inner ℂ ((t : ℂ) • z) (E z)) = t ^ 2 * RCLike.re (inner ℂ z (E z)) := by
      rw [inner_smul_left, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul]
      simp only [RCLike.re_to_complex, Complex.re_ofReal_mul]
      ring
    rw [h_conj_re, h_re_t, h_re_t2, h_re_z, h_re_xz] at hnn
    linarith
  have hx_nn : 0 ≤ RCLike.re (inner ℂ x (E x)) := hE.re_inner_nonneg_right x
  have hy_nn : 0 ≤ RCLike.re (inner ℂ y (E y)) := hE.re_inner_nonneg_right y
  by_cases hy0 : RCLike.re (inner ℂ y (E y)) = 0
  · have hb0 : ‖b‖ = 0 := by
      by_contra hne
      have hbpos : 0 < ‖b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      have hq := h_quad (-(RCLike.re (inner ℂ x (E x)) + 1) / (2 * ‖b‖))
      rw [hy0, mul_zero, add_zero] at hq
      have hcalc : 2 * (-(RCLike.re (inner ℂ x (E x)) + 1) / (2 * ‖b‖)) * ‖b‖ =
          -(RCLike.re (inner ℂ x (E x)) + 1) := by field_simp [hbpos.ne']
      linarith
    rw [hb0, zero_pow two_ne_zero]
    exact mul_nonneg hx_nn hy_nn
  · have hypos : 0 < RCLike.re (inner ℂ y (E y)) := lt_of_le_of_ne hy_nn (Ne.symm hy0)
    have hq := h_quad (-‖b‖ / RCLike.re (inner ℂ y (E y)))
    have hcalc : RCLike.re (inner ℂ x (E x)) + 2 * (-‖b‖ / RCLike.re (inner ℂ y (E y))) * ‖b‖ +
        (-‖b‖ / RCLike.re (inner ℂ y (E y))) ^ 2 * RCLike.re (inner ℂ y (E y)) =
        RCLike.re (inner ℂ x (E x)) - ‖b‖ ^ 2 / RCLike.re (inner ℂ y (E y)) := by
      field_simp [hypos.ne']
      ring
    rw [hcalc] at hq
    have hdiv : ‖b‖ ^ 2 / RCLike.re (inner ℂ y (E y)) ≤ RCLike.re (inner ℂ x (E x)) := by linarith
    exact (div_le_iff₀ hypos).mp hdiv

lemma pos_op_norm_apply_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E : H →L[ℂ] H) (hE : E.IsPositive)
    (h_unit : ∀ ψ : H, ‖ψ‖ = 1 → RCLike.re (inner ℂ ψ (E ψ)) ≤ 1) (x : H) :
    ‖E x‖ ≤ ‖x‖ := by
  have h_le : ∀ z : H, RCLike.re (inner ℂ z (E z)) ≤ ‖z‖ ^ 2 := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have h1 : ‖((‖z‖⁻¹ : ℝ) : ℂ) • z‖ = 1 := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_mul_cancel₀ hz_pos.ne']
      have hu := h_unit _ h1
      rw [map_smul, inner_smul_left, inner_smul_right] at hu
      simp only [Complex.conj_ofReal] at hu
      have hre : RCLike.re (((‖z‖⁻¹ : ℝ) : ℂ) * (((‖z‖⁻¹ : ℝ) : ℂ) * inner ℂ z (E z))) =
          (‖z‖ ^ 2)⁻¹ * RCLike.re (inner ℂ z (E z)) := by
        simp only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
        ring
      rw [hre] at hu
      exact (inv_mul_le_one₀ (sq_pos_of_pos hz_pos)).mp hu
  by_cases hEx : E x = 0
  · rw [hEx, norm_zero]; exact norm_nonneg x
  have hEx_pos : 0 < ‖E x‖ := norm_pos_iff.mpr hEx
  have hcs := pos_op_cauchy_schwarz E hE x (E x)
  have h_in : inner ℂ x (E (E x)) = ((‖E x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hE.inner_left_eq_inner_right, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h_in, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _), ← pow_mul] at hcs
  have h4 : ‖E x‖ ^ 4 ≤ ‖x‖ ^ 2 * ‖E x‖ ^ 2 :=
    hcs.trans (mul_le_mul (h_le x) (h_le (E x)) (hE.re_inner_nonneg_right _) (sq_nonneg _))
  have h2 : ‖E x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [sq_pos_of_pos hEx_pos]
  exact le_of_sq_le_sq h2 (norm_nonneg x)

lemma povm_measure_diff_le {H O : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [MeasurableSpace O] {P : H → MeasureTheory.Measure O} (hP : IsPOVM P)
    {S : Set O} (hS : MeasurableSet S) {ψ₁ ψ₂ : H} (h1 : ‖ψ₁‖ = 1) (h2 : ‖ψ₂‖ = 1) :
    |(P ψ₁ S).toReal - (P ψ₂ S).toReal| ≤ 2 * ‖ψ₁ - ψ₂‖ := by
  obtain ⟨E, hE_pos, hE_eq⟩ := hP.2 S hS
  rw [hE_eq ψ₁ h1, hE_eq ψ₂ h2]
  have h_unit : ∀ ψ : H, ‖ψ‖ = 1 → RCLike.re (inner ℂ ψ (E ψ)) ≤ 1 := by
    intro ψ hψ
    rw [← hE_eq ψ hψ]
    have : MeasureTheory.IsProbabilityMeasure (P ψ) := hP.1 ψ hψ
    have hle1 : P ψ S ≤ 1 := (MeasureTheory.measure_mono (Set.subset_univ S)).trans_eq MeasureTheory.measure_univ
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hle1)
  have h_norm : ∀ x : H, ‖E x‖ ≤ ‖x‖ := pos_op_norm_apply_le E hE_pos h_unit
  have h_diff : RCLike.re (inner ℂ ψ₁ (E ψ₁)) - RCLike.re (inner ℂ ψ₂ (E ψ₂)) =
      RCLike.re (inner ℂ (ψ₁ - ψ₂) (E ψ₁) + inner ℂ ψ₂ (E (ψ₁ - ψ₂))) := by
    rw [map_add, inner_sub_left, map_sub E ψ₁ ψ₂, inner_sub_right]
    simp only [RCLike.re_to_complex, Complex.sub_re]
    ring
  rw [h_diff]
  calc |RCLike.re (inner ℂ (ψ₁ - ψ₂) (E ψ₁) + inner ℂ ψ₂ (E (ψ₁ - ψ₂)))|
      ≤ ‖inner ℂ (ψ₁ - ψ₂) (E ψ₁) + inner ℂ ψ₂ (E (ψ₁ - ψ₂))‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖inner ℂ (ψ₁ - ψ₂) (E ψ₁)‖ + ‖inner ℂ ψ₂ (E (ψ₁ - ψ₂))‖ := norm_add_le _ _
    _ ≤ ‖ψ₁ - ψ₂‖ * ‖E ψ₁‖ + ‖ψ₂‖ * ‖E (ψ₁ - ψ₂)‖ := by
        gcongr <;> exact norm_inner_le_norm _ _
    _ ≤ ‖ψ₁ - ψ₂‖ * ‖ψ₁‖ + ‖ψ₂‖ * ‖ψ₁ - ψ₂‖ := by
        gcongr
        · exact h_norm ψ₁
        · exact h_norm (ψ₁ - ψ₂)
    _ = 2 * ‖ψ₁ - ψ₂‖ := by rw [h1, h2]; ring

end POVM

/-! ### Part 4: Hypercube Embedding, Hybrid Bound, and Disagreement Triangle Inequality -/

noncomputable def sgnBool (b : Bool) : ℝ := if b then 1 else -1

lemma sgnBool_sq (b : Bool) : sgnBool b ^ 2 = 1 := by cases b <;> simp [sgnBool]

lemma sgnBool_mul (a b : Bool) : sgnBool a * sgnBool b = 1 - 2 * (if a ≠ b then (1 : ℝ) else 0) := by
  cases a <;> cases b <;> norm_num [sgnBool]

noncomputable def wVecFun {m : ℕ} (r : ℝ) (z : Fin m → Bool) : Fin (m + 1) → ℝ :=
  Fin.cons (Real.sqrt (1 - r ^ 2)) (fun i : Fin m => r / Real.sqrt m * sgnBool (z i))

noncomputable def wVec {m : ℕ} (r : ℝ) (z : Fin m → Bool) : EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 (wVecFun r z)

lemma wVec_zero {m : ℕ} (r : ℝ) (z : Fin m → Bool) :
    wVec r z 0 = Real.sqrt (1 - r ^ 2) := rfl

lemma wVec_succ {m : ℕ} (r : ℝ) (z : Fin m → Bool) (i : Fin m) :
    wVec r z i.succ = r / Real.sqrt m * sgnBool (z i) := rfl

def dHam {m : ℕ} (z z' : Fin m → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => z i ≠ z' i)).card

def flipCoord {m : ℕ} (z : Fin m → Bool) (i : Fin m) : Fin m → Bool :=
  Function.update z i (!(z i))

lemma flipCoord_invol {m : ℕ} (z : Fin m → Bool) (i : Fin m) :
    flipCoord (flipCoord z i) i = z := by
  ext j
  by_cases h : j = i
  · subst h; simp [flipCoord]
  · simp [flipCoord, Function.update_of_ne h]

lemma wVec_norm {m : ℕ} (hm : 1 ≤ m) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (z : Fin m → Bool) :
    ‖wVec r z‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  simp only [wVec_zero, wVec_succ, Real.norm_eq_abs, sq_abs]
  have h1r : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  rw [Real.sq_sqrt h1r]
  have h_term : ∀ i : Fin m, (r / Real.sqrt m * sgnBool (z i)) ^ 2 = r ^ 2 / m := fun i => by
    rw [mul_pow, sgnBool_sq, mul_one, div_pow, Real.sq_sqrt hm_pos.le]
  simp_rw [h_term, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hm_pos.ne']
  ring

lemma wVec_inner {m : ℕ} (hm : 1 ≤ m) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (z z' : Fin m → Bool) :
    inner ℝ (wVec r z) (wVec r z') = 1 - 2 * r ^ 2 * (dHam z z' : ℝ) / (m : ℝ) := by
  rw [PiLp.inner_apply, Fin.sum_univ_succ]
  simp only [wVec_zero, wVec_succ, RCLike.inner_apply, conj_trivial]
  have h1r : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  rw [Real.mul_self_sqrt h1r]
  have h_term : ∀ i : Fin m,
      (r / Real.sqrt m * sgnBool (z' i)) * (r / Real.sqrt m * sgnBool (z i)) =
        r ^ 2 / m * (1 - 2 * (if z i ≠ z' i then (1 : ℝ) else 0)) := fun i => by
    calc (r / Real.sqrt m * sgnBool (z' i)) * (r / Real.sqrt m * sgnBool (z i))
        = (r / Real.sqrt m) ^ 2 * (sgnBool (z i) * sgnBool (z' i)) := by ring
      _ = r ^ 2 / m * (1 - 2 * (if z i ≠ z' i then (1 : ℝ) else 0)) := by
          rw [div_pow, Real.sq_sqrt hm_pos.le, sgnBool_mul]
  simp_rw [h_term, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, ← Finset.mul_sum,
    Finset.sum_boole]
  unfold dHam
  field_simp [hm_pos.ne']
  ring

lemma wVec_flip_norm {m : ℕ} (hm : 1 ≤ m) {r : ℝ} (hr0 : 0 ≤ r) (z : Fin m → Bool) (i : Fin m) :
    ‖wVec r z - wVec r (flipCoord z i)‖ = 2 * r / Real.sqrt m := by
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  simp only [PiLp.sub_apply, wVec_zero, wVec_succ, Real.norm_eq_abs, sq_abs, sub_self,
    zero_pow two_ne_zero, zero_add]
  rw [Finset.sum_eq_single i]
  · simp only [flipCoord, Function.update_self]
    have hdiff : (sgnBool (z i) - sgnBool (!z i)) ^ 2 = 4 := by
      cases z i <;> norm_num [sgnBool]
    calc (r / Real.sqrt m * sgnBool (z i) - r / Real.sqrt m * sgnBool (!z i)) ^ 2
        = (r / Real.sqrt m) ^ 2 * (sgnBool (z i) - sgnBool (!z i)) ^ 2 := by ring
      _ = (r / Real.sqrt m) ^ 2 * 4 := by rw [hdiff]
      _ = (2 * r / Real.sqrt m) ^ 2 := by ring
  · intro j _ hji
    simp [flipCoord, Function.update_of_ne hji]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

lemma disagree_triangle {n : ℕ} (f g h : EuclideanSpace ℝ (Fin n) → ℤ) :
    disagree f g ≤ disagree h f + disagree h g := by
  unfold disagree
  have hsub : {x | f x ≠ g x} ⊆ {x | h x ≠ f x} ∪ {x | h x ≠ g x} := by
    intro x hx
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hnot
    exact hx (hnot.1.symm.trans hnot.2)
  have h1 : stdGaussian (EuclideanSpace ℝ (Fin n)) {x | f x ≠ g x} ≤
      stdGaussian (EuclideanSpace ℝ (Fin n)) {x | h x ≠ f x} +
      stdGaussian (EuclideanSpace ℝ (Fin n)) {x | h x ≠ g x} :=
    (measure_mono hsub).trans (measure_union_le _ _)
  have h2 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) h1
  rwa [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h2

lemma dHam_le_of_disagree_le {m : ℕ} (hm : 1 ≤ m) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / (8 * Real.pi))
    (z z' : Fin m → Bool)
    (hdis : disagree (ltf (wVec (4 * Real.pi * ε) z) 0) (ltf (wVec (4 * Real.pi * ε) z') 0) ≤ 2 * ε) :
    (dHam z z' : ℝ) ≤ (m : ℝ) / 16 := by
  let r := 4 * Real.pi * ε
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    calc 4 * Real.pi * ε ≤ 4 * Real.pi * (1 / (8 * Real.pi)) := by gcongr
      _ = 1 / 2 := by field_simp; ring
      _ ≤ 1 := by norm_num
  have hw1 : ‖wVec r z‖ = 1 := wVec_norm hm hr0 hr1 z
  have hw2 : ‖wVec r z'‖ = 1 := wVec_norm hm hr0 hr1 z'
  have h21 := (lemma_2_1 (wVec r z) (wVec r z') hw1 hw2 0 0).2
  rw [h21] at hdis
  have harc : Real.arccos (inner ℝ (wVec r z) (wVec r z')) ≤ 2 * Real.pi * ε := by
    have := (div_le_iff₀ Real.pi_pos).mp hdis
    linarith
  have hθ0 : 0 ≤ 2 * Real.pi * ε := by positivity
  have hθpi : 2 * Real.pi * ε ≤ Real.pi := by
    calc 2 * Real.pi * ε ≤ 2 * Real.pi * (1 / (8 * Real.pi)) := by gcongr
      _ = 1 / 4 := by field_simp; ring
      _ ≤ Real.pi := by linarith [Real.pi_gt_three]
  have harc_mem : Real.arccos (inner ℝ (wVec r z) (wVec r z')) ∈ Set.Icc 0 Real.pi :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hcos : Real.cos (2 * Real.pi * ε) ≤ Real.cos (Real.arccos (inner ℝ (wVec r z) (wVec r z'))) :=
    Real.strictAntiOn_cos.antitoneOn harc_mem ⟨hθ0, hθpi⟩ harc
  have hin_abs : |inner ℝ (wVec r z) (wVec r z')| ≤ 1 := by
    simpa [hw1, hw2] using abs_real_inner_le_norm (wVec r z) (wVec r z')
  rw [Real.cos_arccos (abs_le.mp hin_abs).1 (abs_le.mp hin_abs).2, wVec_inner hm hr0 hr1] at hcos
  have hcos_eq : Real.cos (2 * Real.pi * ε) = 1 - 2 * Real.sin (Real.pi * ε) ^ 2 := by
    rw [show (2 * Real.pi * ε : ℝ) = 2 * (Real.pi * ε) by ring, Real.cos_two_mul]
    linarith [Real.sin_sq_add_cos_sq (Real.pi * ε)]
  rw [hcos_eq] at hcos
  have hsin : Real.sin (Real.pi * ε) ^ 2 ≤ (Real.pi * ε) ^ 2 := by
    have h1 : |Real.sin (Real.pi * ε)| ≤ Real.pi * ε := by
      simpa [abs_of_pos (mul_pos Real.pi_pos hε0)] using Real.abs_sin_le_abs (x := Real.pi * ε)
    have h2 : |Real.sin (Real.pi * ε)| ^ 2 ≤ (Real.pi * ε) ^ 2 := by gcongr
    simpa [sq_abs] using h2
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h_bound : 2 * r ^ 2 * (dHam z z' : ℝ) / m ≤ 2 * (Real.pi * ε) ^ 2 := by linarith
  have h_eq_r : 2 * r ^ 2 * (dHam z z' : ℝ) / m =
      2 * (16 * (Real.pi * ε) ^ 2 * ((dHam z z' : ℝ) / m)) := by
    dsimp [r]; ring
  rw [h_eq_r] at h_bound
  have hpi_eps : 0 < (Real.pi * ε) ^ 2 := sq_pos_of_pos (mul_pos Real.pi_pos hε0)
  have h_bound2 : (Real.pi * ε) ^ 2 * (16 * ((dHam z z' : ℝ) / m)) ≤ (Real.pi * ε) ^ 2 * 1 := by
    linarith
  have hdiv : 16 * ((dHam z z' : ℝ) / m) ≤ 1 := le_of_mul_le_mul_left h_bound2 hpi_eps
  have h_res : (dHam z z' : ℝ) ≤ (1 / 16 : ℝ) * m := (div_le_iff₀ hm_pos).mp (by linarith)
  linarith

lemma lift_sub {n : ℕ} {Ω : Type} (U₁ U₂ : ExSpace n ≃ₗᵢ[ℂ] ExSpace n)
    (f : lp (fun _ : Ω => ExSpace n) 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (hU : ∀ x : ExSpace n, ‖U₁ x - U₂ x‖ ≤ δ * ‖x‖) :
    ‖QExLearner.lift U₁ f - QExLearner.lift U₂ f‖ ≤ δ * ‖f‖ := by
  have h_norm : ‖QExLearner.lift U₁ f - QExLearner.lift U₂ f‖ ≤ ‖(δ : ℂ) • f‖ := by
    refine lp.norm_mono (p := 2) (by norm_num) fun ω => ?_
    change ‖U₁ (f ω) - U₂ (f ω)‖ ≤ ‖(δ : ℂ) • (f ω)‖
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hδ]
    exact hU (f ω)
  have h_smul : ‖(δ : ℂ) • f‖ = δ * ‖f‖ := by
    rw [lp.norm_const_smul (by norm_num), Complex.norm_real, Real.norm_of_nonneg hδ]
  exact h_norm.trans_eq h_smul

lemma lift_norm {n : ℕ} {Ω : Type} (U : ExSpace n ≃ₗᵢ[ℂ] ExSpace n)
    (f : lp (fun _ : Ω => ExSpace n) 2) :
    ‖QExLearner.lift U f‖ = ‖f‖ := by
  refine le_antisymm ?_ ?_
  · refine lp.norm_mono (p := 2) (by norm_num) fun ω => ?_
    change ‖U (f ω)‖ ≤ ‖f ω‖
    rw [U.norm_map]
  · refine lp.norm_mono (p := 2) (by norm_num) fun ω => ?_
    change ‖f ω‖ ≤ ‖U (f ω)‖
    rw [U.norm_map]

lemma lift_linear_sub {n : ℕ} {Ω : Type} (U : ExSpace n ≃ₗᵢ[ℂ] ExSpace n)
    (f g : lp (fun _ : Ω => ExSpace n) 2) :
    QExLearner.lift U f - QExLearner.lift U g = QExLearner.lift U (f - g) := by
  refine lp.ext (funext fun ω => ?_)
  change U (f ω) - U (g ω) = U (f ω - g ω)
  rw [map_sub]

lemma stateAt_norm {n : ℕ} (L : QExLearner n) (U : ExSpace n ≃ₗᵢ[ℂ] ExSpace n) (t : ℕ) :
    ‖L.stateAt U t‖ = 1 := by
  induction t with
  | zero => exact L.init_norm
  | succ t ih =>
      simp only [QExLearner.stateAt, LinearIsometryEquiv.norm_map, lift_norm, ih]

lemma stateAt_sub_norm {n : ℕ} (L : QExLearner n) (U₁ U₂ : ExSpace n ≃ₗᵢ[ℂ] ExSpace n)
    {δ : ℝ} (hδ : 0 ≤ δ) (hU : ∀ x : ExSpace n, ‖U₁ x - U₂ x‖ ≤ δ * ‖x‖) (t : ℕ) :
    ‖L.stateAt U₁ t - L.stateAt U₂ t‖ ≤ (t : ℝ) * δ := by
  have hU_symm : ∀ x : ExSpace n, ‖U₁.symm x - U₂.symm x‖ ≤ δ * ‖x‖ := fun x => by
    calc ‖U₁.symm x - U₂.symm x‖
        = ‖U₂ (U₁.symm x - U₂.symm x)‖ := (U₂.norm_map _).symm
      _ = ‖U₂ (U₁.symm x) - x‖ := by rw [map_sub, U₂.apply_symm_apply]
      _ = ‖U₂ (U₁.symm x) - U₁ (U₁.symm x)‖ := by rw [U₁.apply_symm_apply]
      _ = ‖U₁ (U₁.symm x) - U₂ (U₁.symm x)‖ := norm_sub_rev _ _
      _ ≤ δ * ‖U₁.symm x‖ := hU _
      _ = δ * ‖x‖ := by rw [U₁.symm.norm_map]
  induction t with
  | zero => simp [QExLearner.stateAt]
  | succ t ih =>
      simp only [QExLearner.stateAt, Nat.cast_add, Nat.cast_one]
      rw [← map_sub (L.V t), (L.V t).norm_map]
      let M₁ := if L.adj t then U₁.symm else U₁
      let M₂ := if L.adj t then U₂.symm else U₂
      have hM : ∀ x : ExSpace n, ‖M₁ x - M₂ x‖ ≤ δ * ‖x‖ := by
        intro x
        by_cases h : L.adj t = true
        · simp [M₁, M₂, h, hU_symm]
        · simp [M₁, M₂, h, hU]
      calc ‖QExLearner.lift M₁ (L.stateAt U₁ t) - QExLearner.lift M₂ (L.stateAt U₂ t)‖
          = ‖(QExLearner.lift M₁ (L.stateAt U₁ t) - QExLearner.lift M₁ (L.stateAt U₂ t)) +
              (QExLearner.lift M₁ (L.stateAt U₂ t) - QExLearner.lift M₂ (L.stateAt U₂ t))‖ := by
              congr 1; abel
        _ ≤ ‖QExLearner.lift M₁ (L.stateAt U₁ t) - QExLearner.lift M₁ (L.stateAt U₂ t)‖ +
              ‖QExLearner.lift M₁ (L.stateAt U₂ t) - QExLearner.lift M₂ (L.stateAt U₂ t)‖ :=
              norm_add_le _ _
        _ ≤ ‖L.stateAt U₁ t - L.stateAt U₂ t‖ + δ * ‖L.stateAt U₂ t‖ := by
              gcongr
              · rw [lift_linear_sub, lift_norm]
              · exact lift_sub M₁ M₂ (L.stateAt U₂ t) hδ hM
        _ ≤ (t : ℝ) * δ + δ * 1 := by rw [stateAt_norm]; gcongr
        _ = ((t : ℝ) + 1) * δ := by ring

end Aux_wqexlb

open QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (8 * Real.pi) →
      ∀ ψ0 : ExSpace n, ‖ψ0‖ = 1 →
      ∀ L : QExLearner n,
        (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
          ∀ U : ExSpace n ≃ₗᵢ[ℂ] ExSpace n, IsQEXCont ψ0 w U → L.Succeeds U w ε) →
          c * (n : ℝ) ^ (1 / 4 : ℝ) / Real.sqrt ε ≤ L.T := by
  refine ⟨1 / (256 * Real.sqrt Real.pi), by positivity, ?_⟩
  intro n hn ε hε_pos hε_le ψ0 hψ0 L hL
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  let r : ℝ := 4 * Real.pi * ε
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    calc 4 * Real.pi * ε ≤ 4 * Real.pi * (1 / (8 * Real.pi)) := by gcongr
      _ = 1 / 2 := by field_simp; ring
      _ ≤ 1 := by norm_num
  -- Reference state φ0 and fixed unitary V0 mapping ψ0 ↦ φ0
  let φ0 : ExSpace (m + 1) := Aux_wqexlb.exVec 0
  have hφ0_norm : ‖φ0‖ = 1 := Aux_wqexlb.exVec_norm 0
  obtain ⟨V0, hV0⟩ := Aux_wqexlb.unit_phase_householder ψ0 φ0 hψ0 hφ0_norm
  -- Construct Householder oracles U z for z : Fin m → Bool
  let Z := Fin m → Bool
  let ψ : Z → ExSpace (m + 1) := fun z => Aux_wqexlb.exVec (Aux_wqexlb.wVec r z)
  have hψ_norm : ∀ z : Z, ‖ψ z‖ = 1 := fun z => Aux_wqexlb.exVec_norm _
  have h_inner_φψ : ∀ z : Z, (inner ℂ φ0 (ψ z)).im = 0 ∧ 0 ≤ (inner ℂ φ0 (ψ z)).re := by
    intro z
    dsimp [φ0, ψ]
    rw [Aux_wqexlb.exVec_inner]
    refine ⟨by simp, ?_⟩
    simp only [Complex.ofReal_re, sub_nonneg]
    unfold disagree
    have hle1 : ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin (m + 1)))
        {x | ltf 0 0 x ≠ ltf (Aux_wqexlb.wVec r z) 0 x} ≤ 1 :=
      (MeasureTheory.measure_mono (Set.subset_univ _)).trans_eq MeasureTheory.measure_univ
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hle1)
  have h_refl : ∀ z : Z, ∃ hv : φ0 + ψ z ≠ 0, Aux_wqexlb.householderEquiv hv φ0 = ψ z :=
    fun z => Aux_wqexlb.householderEquiv_apply_of_real_inner hφ0_norm (hψ_norm z)
      (h_inner_φψ z).1 (h_inner_φψ z).2
  let R : Z → ExSpace (m + 1) ≃ₗᵢ[ℂ] ExSpace (m + 1) :=
    fun z => Aux_wqexlb.householderEquiv (h_refl z).choose
  let U : Z → ExSpace (m + 1) ≃ₗᵢ[ℂ] ExSpace (m + 1) :=
    fun z => V0.trans (R z)
  have hQEX : ∀ z : Z, IsQEXCont ψ0 (Aux_wqexlb.wVec r z) (U z) := by
    intro z
    have hUz : U z ψ0 = ψ z := by
      change R z (V0 ψ0) = ψ z
      rw [hV0]
      exact (h_refl z).choose_spec
    unfold IsQEXCont
    rw [hUz]
    exact (Aux_wqexlb.gaussExampleState_memLp (Aux_wqexlb.wVec r z)).coeFn_toLp
  -- Bound on neighboring oracle step Δ
  let Δ : ℝ := 16 * Real.sqrt (Real.pi * ε / Real.sqrt m)
  have hΔ_nonneg : 0 ≤ Δ := by positivity
  have hU_flip : ∀ (z : Z) (i : Fin m) (f : ExSpace (m + 1)),
      ‖U z f - U (Aux_wqexlb.flipCoord z i) f‖ ≤ Δ * ‖f‖ := by
    intro z i f
    let z' := Aux_wqexlb.flipCoord z i
    have h_R : ‖R z (V0 f) - R z' (V0 f)‖ ≤ 4 * Real.sqrt 2 * ‖ψ z - ψ z'‖ * ‖V0 f‖ :=
      Aux_wqexlb.householderEquiv_sub_norm_le hφ0_norm (hψ_norm z)
        (h_inner_φψ z).2 (h_refl z).choose (h_refl z').choose (V0 f)
    rw [V0.norm_map] at h_R
    have hwz : ‖Aux_wqexlb.wVec r z‖ = 1 := Aux_wqexlb.wVec_norm hm hr0 hr1 z
    have hwz' : ‖Aux_wqexlb.wVec r z'‖ = 1 := Aux_wqexlb.wVec_norm hm hr0 hr1 z'
    have h_dis : disagree (ltf (Aux_wqexlb.wVec r z) 0) (ltf (Aux_wqexlb.wVec r z') 0) ≤
        r / Real.sqrt m := by
      have h21 := (lemma_2_1 (Aux_wqexlb.wVec r z) (Aux_wqexlb.wVec r z') hwz hwz' 0 0).1
      rw [sub_zero, abs_zero, zero_div, add_zero, Aux_wqexlb.wVec_flip_norm hm hr0 z i] at h21
      rw [show 2 * r / Real.sqrt m / 2 = r / Real.sqrt m by ring] at h21
      exact h21
    have h_ψ_sq : ‖ψ z - ψ z'‖ ^ 2 ≤ 2 * (r / Real.sqrt m) := by
      dsimp [ψ]
      rw [Aux_wqexlb.exVec_norm_sub_sq]
      linarith
    have h_ψ : ‖ψ z - ψ z'‖ ≤ Real.sqrt (2 * (r / Real.sqrt m)) := by
      rw [← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt h_ψ_sq
    have h_calc : 4 * Real.sqrt 2 * Real.sqrt (2 * (r / Real.sqrt m)) = Δ := by
      dsimp [Δ, r]
      have h_in : 2 * (4 * Real.pi * ε / Real.sqrt m) = 8 * (Real.pi * ε / Real.sqrt m) := by ring
      rw [h_in, Real.sqrt_mul (by norm_num), show (8 : ℝ) = 2 * 4 by norm_num,
        Real.sqrt_mul (by norm_num)]
      have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      have h4 : Real.sqrt 4 = 2 := by norm_num
      rw [h4]
      calc 4 * Real.sqrt 2 * (Real.sqrt 2 * 2 * Real.sqrt (Real.pi * ε / Real.sqrt m))
          = 8 * (Real.sqrt 2 * Real.sqrt 2) * Real.sqrt (Real.pi * ε / Real.sqrt m) := by ring
        _ = 8 * 2 * Real.sqrt (Real.pi * ε / Real.sqrt m) := by rw [h22]
        _ = 16 * Real.sqrt (Real.pi * ε / Real.sqrt m) := by ring
    calc ‖U z f - U z' f‖ = ‖R z (V0 f) - R z' (V0 f)‖ := rfl
      _ ≤ 4 * Real.sqrt 2 * ‖ψ z - ψ z'‖ * ‖f‖ := h_R
      _ ≤ 4 * Real.sqrt 2 * Real.sqrt (2 * (r / Real.sqrt m)) * ‖f‖ := by gcongr
      _ = Δ * ‖f‖ := by rw [h_calc]
  have h_state_diff : ∀ (z : Z) (i : Fin m),
      ‖L.stateAt (U z) L.T - L.stateAt (U (Aux_wqexlb.flipCoord z i)) L.T‖ ≤ (L.T : ℝ) * Δ :=
    fun z i => Aux_wqexlb.stateAt_sub_norm L (U z) (U (Aux_wqexlb.flipCoord z i)) hΔ_nonneg
      (hU_flip z i) L.T
  -- Extract success events S z and build measurable partition cells
  have h_succ : ∀ z : Z, L.Succeeds (U z) (Aux_wqexlb.wVec r z) ε :=
    fun z => hL (Aux_wqexlb.wVec r z) (Aux_wqexlb.wVec_norm hm hr0 hr1 z) (U z) (hQEX z)
  let S : Z → Set L.O := fun z => (h_succ z).choose
  have hS_meas : ∀ z : Z, MeasurableSet (S z) := fun z => (h_succ z).choose_spec.1
  have hS_sub : ∀ z : Z, S z ⊆ {o | disagree (L.hyp o) (ltf (Aux_wqexlb.wVec r z) 0) ≤ ε} :=
    fun z => (h_succ z).choose_spec.2.1
  have hS_prob : ∀ z : Z, (2 / 3 : ENNReal) ≤ L.meas (L.stateAt (U z) L.T) (S z) :=
    fun z => (h_succ z).choose_spec.2.2
  let N := Fintype.card Z
  let enum : Fin N ≃ Z := (Fintype.equivFin Z).symm
  let C : Fin N → Set L.O := fun k => S (enum k) \ ⋃ j ∈ Finset.Iio k, S (enum j)
  let U_all : Set L.O := ⋃ k : Fin N, S (enum k)
  let z0 : Z := fun _ => true
  let cell : Z → Set L.O := fun z =>
    if z = z0 then C (enum.symm z) ∪ U_allᶜ else C (enum.symm z)
  have hC_meas : ∀ k : Fin N, MeasurableSet (C k) := fun k =>
    (hS_meas (enum k)).diff (Finset.measurableSet_biUnion _ fun j _ => hS_meas (enum j))
  have hU_all_meas : MeasurableSet U_all :=
    MeasurableSet.iUnion fun k => hS_meas (enum k)
  have hcell_meas : ∀ z : Z, MeasurableSet (cell z) := by
    intro z
    dsimp [cell]
    split_ifs
    · exact (hC_meas _).union hU_all_meas.compl
    · exact hC_meas _
  have hC_disj : Pairwise (fun a b => Disjoint (C a) (C b)) := by
    intro a b hab
    rw [Set.disjoint_iff]
    intro o ⟨hoa, hob⟩
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact hob.2 (Set.mem_biUnion (Finset.mem_Iio.mpr hlt) hoa.1)
    · exact hoa.2 (Set.mem_biUnion (Finset.mem_Iio.mpr hgt) hob.1)
  have hC_sub_U : ∀ k : Fin N, C k ⊆ U_all := fun k _ ho =>
    Set.mem_iUnion.mpr ⟨k, ho.1⟩
  have hcell_disj : Pairwise (fun a b => Disjoint (cell a) (cell b)) := by
    intro a b hab
    rw [Set.disjoint_iff]
    intro o ⟨hoa, hob⟩
    have ha_ne : enum.symm a ≠ enum.symm b := fun h => hab (enum.symm.injective h)
    dsimp [cell] at hoa hob
    split_ifs at hoa hob with ha0 hb0
    · exact hab (ha0.trans hb0.symm)
    · rcases hoa with hoa | hoa
      · exact (Set.disjoint_iff.mp (hC_disj ha_ne)) ⟨hoa, hob⟩
      · exact hoa (hC_sub_U _ hob)
    · rcases hob with hob | hob
      · exact (Set.disjoint_iff.mp (hC_disj ha_ne)) ⟨hoa, hob⟩
      · exact hob (hC_sub_U _ hoa)
    · exact (Set.disjoint_iff.mp (hC_disj ha_ne)) ⟨hoa, hob⟩
  have hC_cover : ⋃ k : Fin N, C k = U_all := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset hC_sub_U
    · intro o ho
      rw [Set.mem_iUnion] at ho
      let s := Finset.univ.filter (fun k : Fin N => o ∈ S (enum k))
      have hs : s.Nonempty := by
        obtain ⟨k, hk⟩ := ho
        exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
      let k₀ := s.min' hs
      have hk₀_mem : k₀ ∈ s := Finset.min'_mem s hs
      refine Set.mem_iUnion.mpr ⟨k₀, (Finset.mem_filter.mp hk₀_mem).2, ?_⟩
      intro ho'
      simp only [Set.mem_iUnion, exists_prop] at ho'
      obtain ⟨j, hj, hoj⟩ := ho'
      have hj_mem : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hoj⟩
      have hle : k₀ ≤ j := Finset.min'_le s j hj_mem
      exact absurd (Finset.mem_Iio.mp hj) (not_lt.mpr hle)
  have hcell_cover : ⋃ z : Z, cell z = Set.univ := by
    ext o
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases ho : o ∈ U_all
    · rw [← hC_cover, Set.mem_iUnion] at ho
      obtain ⟨k, hk⟩ := ho
      refine ⟨enum k, ?_⟩
      dsimp [cell]
      rw [Equiv.symm_apply_apply]
      split_ifs
      · exact Or.inl hk
      · exact hk
    · refine ⟨z0, ?_⟩
      dsimp [cell]
      rw [if_pos rfl]
      exact Or.inr ho
  have h_good_cell : ∀ (z z' : Z) (o : L.O), o ∈ S z → o ∈ cell z' →
      (Aux_wqexlb.dHam z z' : ℝ) ≤ (m : ℝ) / 16 := by
    intro z z' o hoS hoc
    have hoU : o ∈ U_all := Set.mem_iUnion.mpr ⟨enum.symm z, by simpa using hoS⟩
    have hoC : o ∈ C (enum.symm z') := by
      dsimp [cell] at hoc
      split_ifs at hoc
      · rcases hoc with h | h
        · exact h
        · exact (h hoU).elim
      · exact hoc
    have hoS' : o ∈ S z' := by simpa using hoC.1
    have hdis1 : disagree (L.hyp o) (ltf (Aux_wqexlb.wVec r z) 0) ≤ ε := hS_sub z hoS
    have hdis2 : disagree (L.hyp o) (ltf (Aux_wqexlb.wVec r z') 0) ≤ ε := hS_sub z' hoS'
    have hdis : disagree (ltf (Aux_wqexlb.wVec r z) 0) (ltf (Aux_wqexlb.wVec r z') 0) ≤ 2 * ε :=
      (Aux_wqexlb.disagree_triangle _ _ (L.hyp o)).trans (by linarith)
    exact Aux_wqexlb.dHam_le_of_disagree_le hm hε_pos hε_le z z' hdis
  -- Probability measures under each oracle U z
  let μ : Z → MeasureTheory.Measure L.O := fun z => L.meas (L.stateAt (U z) L.T)
  have hμ_prob : ∀ z : Z, MeasureTheory.IsProbabilityMeasure (μ z) :=
    fun z => L.meas_povm.1 _ (Aux_wqexlb.stateAt_norm L (U z) L.T)
  have h_cell_sum : ∀ z : Z, ∑ z' : Z, (μ z (cell z')).toReal = 1 := by
    intro z
    have := hμ_prob z
    have h_meas_union : μ z (⋃ z' ∈ (Finset.univ : Finset Z), cell z') =
        ∑ z' : Z, μ z (cell z') :=
      MeasureTheory.measure_biUnion_finset
        (fun a _ b _ hab => hcell_disj hab) (fun a _ => hcell_meas a)
    have h_univ : (⋃ z' ∈ (Finset.univ : Finset Z), cell z') = Set.univ := by
      simpa using hcell_cover
    rw [h_univ, MeasureTheory.measure_univ] at h_meas_union
    have h_toReal := congrArg ENNReal.toReal h_meas_union.symm
    rw [ENNReal.toReal_sum (fun z' _ => MeasureTheory.measure_ne_top _ _), ENNReal.toReal_one] at h_toReal
    exact h_toReal
  -- Expected Hamming error
  let expHam : Z → ℝ := fun z =>
    ∑ z' : Z, (Aux_wqexlb.dHam z z' : ℝ) * (μ z (cell z')).toReal
  -- Upper bound: expHam z ≤ (3 / 8) * m
  have h_exp_upper : ∀ z : Z, expHam z ≤ (3 / 8 : ℝ) * (m : ℝ) := by
    intro z
    have := hμ_prob z
    let Good : Finset Z := Finset.univ.filter (fun z' : Z => (Aux_wqexlb.dHam z z' : ℝ) ≤ (m : ℝ) / 16)
    have hS_sub_good : S z ⊆ ⋃ z' ∈ Good, cell z' := by
      intro o hoS
      have ho_cov : o ∈ ⋃ z' : Z, cell z' := by rw [hcell_cover]; trivial
      obtain ⟨z', hz'⟩ := Set.mem_iUnion.mp ho_cov
      refine Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ z', ?_⟩) hz'
      exact h_good_cell z z' o hoS hz'
    let p_good : ℝ := ∑ z' ∈ Good, (μ z (cell z')).toReal
    have hp_good_eq : p_good = (μ z (⋃ z' ∈ Good, cell z')).toReal := by
      rw [MeasureTheory.measure_biUnion_finset
        (fun a _ b _ hab => hcell_disj hab) (fun a _ => hcell_meas a)]
      exact (ENNReal.toReal_sum (fun z' _ => MeasureTheory.measure_ne_top _ _)).symm
    have hp_good_ge : (2 / 3 : ℝ) ≤ p_good := by
      rw [hp_good_eq]
      have h_enn : (2 / 3 : ENNReal) ≤ μ z (⋃ z' ∈ Good, cell z') :=
        (hS_prob z).trans (MeasureTheory.measure_mono hS_sub_good)
      have h_tr := ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) h_enn
      have h23 : ((2 / 3 : ENNReal)).toReal = (2 / 3 : ℝ) := by
        rw [ENNReal.toReal_div]; norm_num
      rwa [h23] at h_tr
    let p_bad : ℝ := ∑ z' ∈ Goodᶜ, (μ z (cell z')).toReal
    have hp_sum : p_good + p_bad = 1 := by
      rw [← h_cell_sum z]
      exact Finset.sum_add_sum_compl Good (fun z' => (μ z (cell z')).toReal)
    have hp_bad_eq : p_bad = 1 - p_good := by linarith
    have h_split : expHam z =
        ∑ z' ∈ Good, (Aux_wqexlb.dHam z z' : ℝ) * (μ z (cell z')).toReal +
        ∑ z' ∈ Goodᶜ, (Aux_wqexlb.dHam z z' : ℝ) * (μ z (cell z')).toReal :=
      (Finset.sum_add_sum_compl Good (fun z' => (Aux_wqexlb.dHam z z' : ℝ) * (μ z (cell z')).toReal)).symm
    have h_good_le : ∑ z' ∈ Good, (Aux_wqexlb.dHam z z' : ℝ) * (μ z (cell z')).toReal ≤
        ((m : ℝ) / 16) * p_good := by
      calc ∑ z' ∈ Good, (Aux_wqexlb.dHam z z' : ℝ) * (μ z (cell z')).toReal
          ≤ ∑ z' ∈ Good, ((m : ℝ) / 16) * (μ z (cell z')).toReal := by
            refine Finset.sum_le_sum fun z' hz' => ?_
            exact mul_le_mul_of_nonneg_right (Finset.mem_filter.mp hz').2 ENNReal.toReal_nonneg
        _ = ((m : ℝ) / 16) * p_good := (Finset.mul_sum Good _ _).symm
    have h_bad_le : ∑ z' ∈ Goodᶜ, (Aux_wqexlb.dHam z z' : ℝ) * (μ z (cell z')).toReal ≤
        (m : ℝ) * p_bad := by
      calc ∑ z' ∈ Goodᶜ, (Aux_wqexlb.dHam z z' : ℝ) * (μ z (cell z')).toReal
          ≤ ∑ z' ∈ Goodᶜ, (m : ℝ) * (μ z (cell z')).toReal := by
            refine Finset.sum_le_sum fun z' _ => ?_
            have hd_le : (Aux_wqexlb.dHam z z' : ℝ) ≤ m := by
              exact_mod_cast (Finset.card_filter_le _ _).trans_eq (by simp)
            exact mul_le_mul_of_nonneg_right hd_le ENNReal.toReal_nonneg
        _ = (m : ℝ) * p_bad := (Finset.mul_sum Goodᶜ _ _).symm
    calc expHam z
        ≤ ((m : ℝ) / 16) * p_good + (m : ℝ) * p_bad := by linarith
      _ = (m : ℝ) * (1 - (15 / 16 : ℝ) * p_good) := by rw [hp_bad_eq]; ring
      _ ≤ (m : ℝ) * (1 - (15 / 16 : ℝ) * (2 / 3 : ℝ)) := by nlinarith
      _ = (3 / 8 : ℝ) * (m : ℝ) := by ring
  -- Lower bound via Assouad's method
  let A : Fin m → Set L.O := fun i =>
    ⋃ z' ∈ Finset.univ.filter (fun z' : Z => z' i = true), cell z'
  let A' : Fin m → Set L.O := fun i =>
    ⋃ z' ∈ Finset.univ.filter (fun z' : Z => z' i = false), cell z'
  have hA_meas : ∀ i : Fin m, MeasurableSet (A i) := fun i =>
    Finset.measurableSet_biUnion _ fun z' _ => hcell_meas z'
  have hA_sum : ∀ (z : Z) (i : Fin m),
      (μ z (A i)).toReal + (μ z (A' i)).toReal = 1 := by
    intro z i
    have := hμ_prob z
    have hA_eq : (μ z (A i)).toReal =
        ∑ z' ∈ Finset.univ.filter (fun z' : Z => z' i = true), (μ z (cell z')).toReal := by
      rw [MeasureTheory.measure_biUnion_finset (fun a _ b _ hab => hcell_disj hab)
        (fun a _ => hcell_meas a)]
      exact ENNReal.toReal_sum (fun z' _ => MeasureTheory.measure_ne_top _ _)
    have hA'_eq : (μ z (A' i)).toReal =
        ∑ z' ∈ Finset.univ.filter (fun z' : Z => z' i = false), (μ z (cell z')).toReal := by
      rw [MeasureTheory.measure_biUnion_finset (fun a _ b _ hab => hcell_disj hab)
        (fun a _ => hcell_meas a)]
      exact ENNReal.toReal_sum (fun z' _ => MeasureTheory.measure_ne_top _ _)
    rw [hA_eq, hA'_eq]
    have h_part := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset Z)
      (fun z' : Z => z' i = true) (fun z' => (μ z (cell z')).toReal)
    simp only [Bool.not_eq_true] at h_part
    rw [h_part, h_cell_sum z]
  let err : Z → Fin m → ℝ := fun z i =>
    if z i = true then (μ z (A' i)).toReal else (μ z (A i)).toReal
  have h_exp_eq : ∀ z : Z, expHam z = ∑ i : Fin m, err z i := by
    intro z
    have := hμ_prob z
    dsimp [expHam]
    have h_dHam : ∀ z' : Z, (Aux_wqexlb.dHam z z' : ℝ) =
        ∑ i : Fin m, (if z i ≠ z' i then (1 : ℝ) else 0) := fun z' => by
      unfold Aux_wqexlb.dHam
      simp [Finset.card_filter]
    simp_rw [h_dHam, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h_term : ∀ z' : Z, (if z i ≠ z' i then (1 : ℝ) else 0) * (μ z (cell z')).toReal =
        (if z' i ≠ z i then (μ z (cell z')).toReal else 0) := fun z' => by
      by_cases h : z i ≠ z' i <;> simp [h, ne_comm]
    simp_rw [h_term, ← Finset.sum_filter]
    dsimp [err]
    by_cases hzi : z i = true
    · rw [if_pos hzi]
      have h_filt : Finset.univ.filter (fun z' : Z => z' i ≠ z i) =
          Finset.univ.filter (fun z' : Z => z' i = false) := by
        ext z'; simp [hzi]
      rw [h_filt, MeasureTheory.measure_biUnion_finset (fun a _ b _ hab => hcell_disj hab)
        (fun a _ => hcell_meas a), ENNReal.toReal_sum (fun z' _ => MeasureTheory.measure_ne_top _ _)]
    · have hz_false : z i = false := Bool.eq_false_iff.mpr hzi
      rw [if_neg hzi]
      have h_filt : Finset.univ.filter (fun z' : Z => z' i ≠ z i) =
          Finset.univ.filter (fun z' : Z => z' i = true) := by
        ext z'; simp [hz_false]
      rw [h_filt, MeasureTheory.measure_biUnion_finset (fun a _ b _ hab => hcell_disj hab)
        (fun a _ => hcell_meas a), ENNReal.toReal_sum (fun z' _ => MeasureTheory.measure_ne_top _ _)]
  have h_pair : ∀ (z : Z) (i : Fin m),
      err z i + err (Aux_wqexlb.flipCoord z i) i ≥ 1 - 2 * ((L.T : ℝ) * Δ) := by
    intro z i
    let z' := Aux_wqexlb.flipCoord z i
    have h_povm : |(μ z (A i)).toReal - (μ z' (A i)).toReal| ≤ 2 * ((L.T : ℝ) * Δ) := by
      have h1 := Aux_wqexlb.povm_measure_diff_le L.meas_povm (hA_meas i)
        (Aux_wqexlb.stateAt_norm L (U z) L.T) (Aux_wqexlb.stateAt_norm L (U z') L.T)
      exact h1.trans (mul_le_mul_of_nonneg_left (h_state_diff z i) (by norm_num))
    have h_abs := abs_sub_le_iff.mp h_povm
    dsimp [err]
    have hflip : z' i = !(z i) := by simp [z', Aux_wqexlb.flipCoord]
    by_cases hzi : z i = true
    · have hzi' : Aux_wqexlb.flipCoord z i i = false := by simpa [z'] using (by simp [hflip, hzi] : z' i = false)
      rw [if_pos hzi, if_neg (by simp [hzi'])]
      linarith [hA_sum z i]
    · have hzi_false : z i = false := Bool.eq_false_iff.mpr hzi
      have hzi' : Aux_wqexlb.flipCoord z i i = true := by simpa [z'] using (by simp [hflip, hzi_false] : z' i = true)
      rw [if_neg hzi, if_pos hzi']
      linarith [hA_sum z' i]
  have h_sum_lower : (m : ℝ) * (N : ℝ) * (1 - 2 * ((L.T : ℝ) * Δ)) ≤ 2 * ∑ z : Z, expHam z := by
    simp_rw [h_exp_eq]
    rw [Finset.sum_comm, Finset.mul_sum]
    have h_each_i : ∀ i : Fin m, (N : ℝ) * (1 - 2 * ((L.T : ℝ) * Δ)) ≤ 2 * ∑ z : Z, err z i := by
      intro i
      let e : Equiv.Perm Z :=
        { toFun := fun z => Aux_wqexlb.flipCoord z i
          invFun := fun z => Aux_wqexlb.flipCoord z i
          left_inv := fun z => Aux_wqexlb.flipCoord_invol z i
          right_inv := fun z => Aux_wqexlb.flipCoord_invol z i }
      have h_perm : ∑ z : Z, err (Aux_wqexlb.flipCoord z i) i = ∑ z : Z, err z i :=
        Equiv.sum_comp e (fun z => err z i)
      have h_dbl : 2 * ∑ z : Z, err z i = ∑ z : Z, (err z i + err (Aux_wqexlb.flipCoord z i) i) := by
        rw [Finset.sum_add_distrib, h_perm, two_mul]
      rw [h_dbl]
      calc (N : ℝ) * (1 - 2 * ((L.T : ℝ) * Δ))
          = ∑ _z : Z, (1 - 2 * ((L.T : ℝ) * Δ)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ ∑ z : Z, (err z i + err (Aux_wqexlb.flipCoord z i) i) :=
            Finset.sum_le_sum fun z _ => h_pair z i
    calc (m : ℝ) * (N : ℝ) * (1 - 2 * ((L.T : ℝ) * Δ))
        = ∑ _i : Fin m, (N : ℝ) * (1 - 2 * ((L.T : ℝ) * Δ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
      _ ≤ ∑ i : Fin m, 2 * ∑ z : Z, err z i := Finset.sum_le_sum fun i _ => h_each_i i
  have h_sum_upper : ∑ z : Z, expHam z ≤ (N : ℝ) * ((3 / 8 : ℝ) * (m : ℝ)) := by
    calc ∑ z : Z, expHam z
        ≤ ∑ _z : Z, ((3 / 8 : ℝ) * (m : ℝ)) := Finset.sum_le_sum fun z _ => h_exp_upper z
      _ = (N : ℝ) * ((3 / 8 : ℝ) * (m : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_comb : (m : ℝ) * (N : ℝ) * (1 - 2 * ((L.T : ℝ) * Δ)) ≤
      (m : ℝ) * (N : ℝ) * (3 / 4 : ℝ) := by
    linarith
  have hN_pos : (0 : ℝ) < N := by
    exact_mod_cast Fintype.card_pos (α := Z)
  have hmN_pos : 0 < (m : ℝ) * (N : ℝ) := mul_pos hm_pos hN_pos
  have h_cancel : 1 - 2 * ((L.T : ℝ) * Δ) ≤ 3 / 4 :=
    le_of_mul_le_mul_left h_comb hmN_pos
  have h_main : (1 / 128 : ℝ) ≤ (L.T : ℝ) * Real.sqrt (Real.pi * ε / Real.sqrt m) := by
    dsimp [Δ] at h_cancel
    linarith
  have h_sqrt_eq : Real.sqrt (Real.pi * ε / Real.sqrt m) =
      Real.sqrt Real.pi * Real.sqrt ε / (m : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul Real.pi_pos.le]
    congr 1
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hm_pos.le]
    norm_num
  rw [h_sqrt_eq] at h_main
  have hm14_pos : 0 < (m : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hm_pos _
  have h_pi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h_eps_pos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε_pos
  have h_m_bound : (1 / (128 * Real.sqrt Real.pi)) * (m : ℝ) ^ (1 / 4 : ℝ) / Real.sqrt ε ≤ (L.T : ℝ) := by
    have h1 : (1 / 128 : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ) ≤ (L.T : ℝ) * (Real.sqrt Real.pi * Real.sqrt ε) := by
      have := (le_div_iff₀ hm14_pos).mp (by
        calc (1 / 128 : ℝ) ≤ (L.T : ℝ) * (Real.sqrt Real.pi * Real.sqrt ε / (m : ℝ) ^ (1 / 4 : ℝ)) := h_main
          _ = ((L.T : ℝ) * (Real.sqrt Real.pi * Real.sqrt ε)) / (m : ℝ) ^ (1 / 4 : ℝ) := by ring)
      exact this
    have h2 : (1 / 128 : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ) / (Real.sqrt Real.pi * Real.sqrt ε) ≤ (L.T : ℝ) :=
      (div_le_iff₀ (mul_pos h_pi_pos h_eps_pos)).mpr h1
    calc (1 / (128 * Real.sqrt Real.pi)) * (m : ℝ) ^ (1 / 4 : ℝ) / Real.sqrt ε
        = (1 / 128 : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ) / (Real.sqrt Real.pi * Real.sqrt ε) := by ring
      _ ≤ (L.T : ℝ) := h2
  have hn_le_2m : ((m + 1 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
    push_cast
    linarith [show (1 : ℝ) ≤ (m : ℝ) by exact_mod_cast hm]
  have hn14_le : ((m + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ) ≤ 2 * (m : ℝ) ^ (1 / 4 : ℝ) := by
    calc ((m + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ)
        ≤ (2 * (m : ℝ)) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hn_le_2m (by norm_num)
      _ = (2 : ℝ) ^ (1 / 4 : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ) :=
          Real.mul_rpow (by norm_num) hm_pos.le
      _ ≤ 2 * (m : ℝ) ^ (1 / 4 : ℝ) := by
          gcongr
          calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
  calc (1 / (256 * Real.sqrt Real.pi)) * ((m + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ) / Real.sqrt ε
      ≤ (1 / (256 * Real.sqrt Real.pi)) * (2 * (m : ℝ) ^ (1 / 4 : ℝ)) / Real.sqrt ε := by
        gcongr
    _ = (1 / (128 * Real.sqrt Real.pi)) * (m : ℝ) ^ (1 / 4 : ℝ) / Real.sqrt ε := by ring
    _ ≤ (L.T : ℝ) := h_m_bound
