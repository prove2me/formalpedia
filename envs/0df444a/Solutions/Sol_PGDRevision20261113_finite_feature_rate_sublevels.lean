-- Prove2me | solution 1 for PGDRevision20261113.finite_feature_rate_sublevels
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-13T10:16:26.542225+00:00
-- url     : https://prove2.me/submissions/134c4064-b260-450b-8512-cbdb248e3841

import Theorems.Thm_PGDRevision20261113_error_band_equivalence
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 2500000
open PGDRevision20261113
open scoped ENNReal BigOperators
noncomputable section

private lemma primitive_hasDerivAt (a : ℝ → ℝ) (ha : Continuous a) (x : ℝ) :
    HasDerivAt (primitive a) (a x) x := by
  exact intervalIntegral.integral_hasDerivAt_right (ha.intervalIntegrable 0 x)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_univ ha.continuousOn x (Set.mem_univ x))
    ha.continuousAt

private lemma primitive_deriv (a : ℝ → ℝ) (ha : Continuous a) : deriv (primitive a) = a :=
  funext fun x => (primitive_hasDerivAt a ha x).deriv

private lemma double_data (a : ℝ → ℝ) (ha : Continuous a) :
    ContDiff ℝ 2 (doublePrimitive a) ∧ deriv (deriv (doublePrimitive a)) = a := by
  have hp : Continuous (primitive a) := continuous_iff_continuousAt.mpr
    fun x => (primitive_hasDerivAt a ha x).continuousAt
  have hp1 : ContDiff ℝ 1 (primitive a) := contDiff_one_iff_deriv.mpr
    ⟨fun x => (primitive_hasDerivAt a ha x).differentiableAt, by rwa [primitive_deriv a ha]⟩
  have hd : deriv (doublePrimitive a) = primitive a := primitive_deriv _ hp
  constructor
  · change ContDiff ℝ (1 + 1) (doublePrimitive a)
    apply contDiff_succ_iff_deriv.mpr
    refine ⟨fun x => (primitive_hasDerivAt _ hp x).differentiableAt, ?_, ?_⟩
    · intro h
      norm_num at h
    · rwa [hd]
  · rw [hd, primitive_deriv a ha]

private lemma surjective_derivative_bound (f : ℝ → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (hf : Differentiable ℝ f) (hd : ∀ x : ℝ, lam ≤ deriv f x) : Function.Surjective f := by
  intro y
  let R := (|y - f 0| + 1) / lam
  have hR : 0 < R := div_pos (by positivity) hlam
  have heq : lam * R = |y - f 0| + 1 := by dsimp [R]; field_simp
  have hr := mul_sub_le_image_sub_of_le_deriv hf hd hR.le
  have hl := mul_sub_le_image_sub_of_le_deriv hf hd (show -R ≤ 0 by linarith)
  have hbracket : y ∈ Set.Icc (f (-R)) (f R) := by
    constructor <;> nlinarith [le_abs_self (y - f 0), neg_abs_le (y - f 0)]
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc (by linarith : -R ≤ R) hf.continuous.continuousOn hbracket
  exact ⟨x, hx⟩

private lemma feature_cont {d : ℕ} (D : FeatureData d) (hD : AdmissibleFeatures D)
    (theta : Fin d → ℝ) : Continuous (featureCurvature D theta) := by
  have hh (j : Fin d) : Continuous (D.feature j) := (hD.2.2.2.2.2 j).1.continuous
  unfold featureCurvature
  fun_prop

private lemma feature_admissible {d : ℕ} (D : FeatureData d) (hD : AdmissibleFeatures D)
    (theta : Fin d → ℝ) (u : ℝ) : AdmissibleProfile (featureProfile D theta) (Real.exp u) := by
  have hk := feature_cont D hD theta
  obtain ⟨hf, hg, hA, _, ⟨lam, hlam, hB⟩, hfeature⟩ := hD
  obtain ⟨hphi, hcurv⟩ := double_data _ hk
  have hpos (x : ℝ) : 0 < featureCurvature D theta x := Real.exp_pos _
  refine ⟨Set.univ_nonempty, isOpen_univ, Set.ordConnected_univ,
    hf.contDiffOn, hg.contDiffOn, hphi.contDiffOn, Real.exp_pos u, ?_, ?_⟩
  · intro t _
    change 0 ≤ deriv (deriv D.f) t ∧ 0 ≤ deriv (deriv D.g) t ∧
      0 < deriv (deriv D.f) t + deriv (deriv D.g) t ∧
      0 < deriv (deriv (doublePrimitive (featureCurvature D theta))) t
    rw [hcurv]
    exact ⟨hA t, by linarith [hB t], by linarith [hA t, hB t], hpos t⟩
  · let f := fun t => Real.exp u * deriv (doublePrimitive (featureCurvature D theta)) t + deriv D.g t
    have hd (t : ℝ) : HasDerivAt f
        (Real.exp u * featureCurvature D theta t + deriv (deriv D.g) t) t := by
      have h := ((hphi.differentiable_deriv_two t).hasDerivAt.const_mul (Real.exp u)).add
        ((hg.differentiable_deriv_two t).hasDerivAt)
      convert h using 1 <;> first | rfl | simp only [hcurv]
    have hs : Function.Surjective f := surjective_derivative_bound f lam hlam
      (fun t => (hd t).differentiableAt) (fun t => by
        rw [(hd t).deriv]
        have hp := mul_pos (Real.exp_pos u) (hpos t)
        linarith [hB t])
    intro y _
    obtain ⟨x, hx⟩ := hs y
    exact ⟨x, Set.mem_univ _, hx⟩

private lemma exp_band_equiv (A B v R : ℝ) (hA : 0 ≤ A) (hB : 0 < B)
    (hR : 0 < R) (hR1 : R < 1) :
    |(Real.exp v - A) / (Real.exp v + B)| ≤ R ↔
      v ≤ Real.log (upperBand A B R) ∧
      (R * B < A → Real.log (lowerBand A B R) ≤ v) := by
  have hU : 0 < upperBand A B R := div_pos (by nlinarith) (by linarith)
  rw [PGDRevision20261113.error_band_equivalence A B (Real.exp v) R hA hB (Real.exp_pos v) hR hR1]
  constructor
  · rintro ⟨hl, hu⟩
    constructor
    · apply Real.exp_le_exp.mp
      rwa [Real.exp_log hU]
    · intro h
      have hL : 0 < lowerBand A B R := div_pos (by linarith) (by linarith)
      apply Real.exp_le_exp.mp
      rwa [Real.exp_log hL]
  · rintro ⟨hu, hl⟩
    constructor
    · by_cases h : R * B < A
      · have hL : 0 < lowerBand A B R := div_pos (by linarith) (by linarith)
        have he := Real.exp_le_exp.mpr (hl h)
        rwa [Real.exp_log hL] at he
      · exact (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith : 0 ≤ 1 + R)).trans
          (Real.exp_pos v).le
    · have he := Real.exp_le_exp.mpr hu
      rwa [Real.exp_log hU] at he

private lemma feature_bands {d : ℕ} (D : FeatureData d) (hD : AdmissibleFeatures D)
    (R : ℝ) (hR : 0 < R) (hR1 : R < 1) (z : ℝ × (Fin d → ℝ)) :
    z ∈ featureSublevel D R ↔ FeatureBands D z R := by
  have hcurv := (double_data (featureCurvature D z.2) (feature_cont D hD z.2)).2
  obtain ⟨_, _, hA, _, ⟨lam, hlam, hB⟩, _⟩ := hD
  change (⨆ t ∈ Set.univ, ENNReal.ofReal |profileError (featureProfile D z.2) (Real.exp z.1) t|) ≤
      ENNReal.ofReal R ↔ _
  rw [iSup_le_iff]
  simp only [iSup_le_iff, Set.mem_univ, forall_true_left, ENNReal.ofReal_le_ofReal_iff hR.le]
  apply forall_congr'
  intro t
  have he : profileError (featureProfile D z.2) (Real.exp z.1) t =
      (Real.exp (z.1 + ∑ j, z.2 j * D.feature j t) - deriv (deriv D.f) t) /
        (Real.exp (z.1 + ∑ j, z.2 j * D.feature j t) + deriv (deriv D.g) t) := by
    simp only [profileError, generatorCurvature, lossCurvature, penaltyCurvature, featureProfile, hcurv]
    rw [Real.exp_add]
    rfl
  rw [he]
  exact exp_band_equiv _ _ _ R (hA t) (by linarith [hB t]) hR hR1

theorem solution : FiniteFeatureDesignClaim := by
  intro d D hD
  refine ⟨feature_admissible D hD, ?_⟩
  intro R hR hR1
  refine ⟨feature_bands D hD R hR hR1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxB := (feature_bands D hD R hR hR1 x).mp hx
  have hyB := (feature_bands D hD R hR hR1 y).mp hy
  apply (feature_bands D hD R hR hR1 _).mpr
  intro t
  have hlin : (a • x + b • y).1 + ∑ j, (a • x + b • y).2 j * D.feature j t =
      a * (x.1 + ∑ j, x.2 j * D.feature j t) + b * (y.1 + ∑ j, y.2 j * D.feature j t) := by
    change a * x.1 + b * y.1 + ∑ j, (a * x.2 j + b * y.2 j) * D.feature j t = _
    simp_rw [add_mul, mul_assoc]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [hlin]
  constructor
  · have h1 := mul_le_mul_of_nonneg_left (hxB t).1 ha
    have h2 := mul_le_mul_of_nonneg_left (hyB t).1 hb
    calc
      _ ≤ a * Real.log (upperBand (deriv (deriv D.f) t) (deriv (deriv D.g) t) R) +
          b * Real.log (upperBand (deriv (deriv D.f) t) (deriv (deriv D.g) t) R) := add_le_add h1 h2
      _ = _ := by rw [← add_mul, hab, one_mul]
  · intro hl
    have h1 := mul_le_mul_of_nonneg_left ((hxB t).2 hl) ha
    have h2 := mul_le_mul_of_nonneg_left ((hyB t).2 hl) hb
    calc
      _ = a * Real.log (lowerBand (deriv (deriv D.f) t) (deriv (deriv D.g) t) R) +
          b * Real.log (lowerBand (deriv (deriv D.f) t) (deriv (deriv D.g) t) R) := by rw [← add_mul, hab, one_mul]
      _ ≤ _ := add_le_add h1 h2
