-- Prove2me | solution 1 for TraceEstimation.Gaussian.two_tails
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-01T19:24:35.689182+00:00
-- url     : https://prove2.me/submissions/d07a674d-acee-417a-b633-1715298e4e61

import Mathlib
import Definitions.Def_TraceEstimation_Shared_gaussianEstimator
import Definitions.Def_TraceEstimation_Shared_IsApproximator


open MeasureTheory ProbabilityTheory Real

namespace TraceGaussianProof

lemma gaussian_sq_mgf (a : ℝ) (ha : 2 * a < 1) :
    Integrable (fun x : ℝ => exp (a * x ^ 2)) (gaussianReal 0 1) ∧
      (∫ x : ℝ, exp (a * x ^ 2) ∂gaussianReal 0 1) =
        (1 - 2 * a) ^ (-(1 : ℝ) / 2) := by
  have hb : 0 < 1 / 2 - a := by linarith
  have hd : 0 < 1 - 2 * a := by linarith
  have hp : 0 < 2 * Real.pi := by positivity
  have hw : ∀ x : ℝ, gaussianPDFReal 0 1 x * exp (a * x ^ 2) =
      (sqrt (2 * Real.pi))⁻¹ * exp (-(1 / 2 - a) * x ^ 2) := by
    intro x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← exp_add]
    congr 2
    ring
  have hwi : Integrable (fun x : ℝ => gaussianPDFReal 0 1 x * exp (a * x ^ 2)) := by
    simp_rw [hw]
    exact (integrable_exp_neg_mul_sq hb).const_mul _
  have hi : Integrable (fun x : ℝ => exp (a * x ^ 2)) (gaussianReal 0 1) := by
    rw [gaussianReal_of_var_ne_zero _ (one_ne_zero : (1 : NNReal) ≠ 0)]
    apply (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)).mpr
    simpa only [toReal_gaussianPDF, smul_eq_mul] using hwi
  refine ⟨hi, ?_⟩
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : NNReal) ≠ 0)]
  simp_rw [smul_eq_mul, hw]
  rw [integral_const_mul, integral_gaussian]
  set R := (sqrt (2 * Real.pi))⁻¹ * sqrt (Real.pi / (1 / 2 - a))
  have hR : 0 ≤ R := by positivity
  have hsq : R ^ 2 * (1 - 2 * a) = 1 := by
    dsimp [R]
    rw [mul_pow, inv_pow, sq_sqrt hp.le, sq_sqrt (by positivity)]
    field_simp
  have hs : ((1 - 2 * a) ^ (-(1 : ℝ) / 2)) ^ 2 * (1 - 2 * a) = 1 := by
    rw [← rpow_natCast, ← rpow_mul hd.le]
    norm_num
    rw [rpow_neg_one, inv_mul_cancel₀ hd.ne']
  apply (sq_eq_sq₀ hR (rpow_nonneg hd.le _)).mp
  nlinarith

lemma gaussian_pi_sq_mgf {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (hd : ∀ i, 2 * d i < 1) :
    Integrable (fun x : ι → ℝ => exp (∑ i, d i * x i ^ 2))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) ∧
    (∫ x : ι → ℝ, exp (∑ i, d i * x i ^ 2)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      ∏ i, (1 - 2 * d i) ^ (-(1 : ℝ) / 2) := by
  classical
  have hc := fun i => gaussian_sq_mgf (d i) (hd i)
  refine ⟨?_, ?_⟩
  · simp_rw [exp_sum]
    exact Integrable.fintype_prod_dep (fun i => (hc i).1)
  · simp_rw [exp_sum]
    rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => exp (d i * x ^ 2))]
    simp_rw [fun i => (hc i).2]

end TraceGaussianProof


open MeasureTheory ProbabilityTheory Real Matrix
open scoped RealInnerProductSpace

namespace TraceGaussianProof

lemma quadratic_spectral {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (x : EuclideanSpace ℝ (Fin n)) :
    x ⬝ᵥ (A *ᵥ x) = ∑ i, hA.eigenvalues i * (hA.eigenvectorBasis.repr x i) ^ 2 := by
  let b := hA.eigenvectorBasis
  let G := Matrix.toEuclideanLin A
  have hs : G.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have heig : ∀ i, G (b i) = hA.eigenvalues i • b i := by
    intro i
    ext j
    exact congrFun (hA.mulVec_eigenvectorBasis i) j
  have hi : ⟪x, G x⟫ = ∑ i, hA.eigenvalues i * (b.repr x i) ^ 2 := by
    rw [← b.sum_inner_mul_inner x (G x)]
    apply Finset.sum_congr rfl
    intro i _
    have hh : ⟪b i, G x⟫ = hA.eigenvalues i * ⟪b i, x⟫ := by
      rw [← hs, heig, real_inner_smul_left]
    rw [hh, b.repr_apply_apply]
    rw [real_inner_comm x (b i)]
    ring
  rw [EuclideanSpace.inner_eq_star_dotProduct] at hi
  simp only [star_trivial] at hi
  change (A *ᵥ x) ⬝ᵥ x = ∑ i, hA.eigenvalues i * (b.repr x i) ^ 2 at hi
  rwa [dotProduct_comm] at hi

lemma single_sample_mgf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (t : ℝ) (ht : ∀ i, 2 * hA.eigenvalues i * t < 1) :
    Integrable (fun x : Fin n → ℝ => exp (t * (x ⬝ᵥ (A *ᵥ x))))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) ∧
    (∫ x : Fin n → ℝ, exp (t * (x ⬝ᵥ (A *ᵥ x)))
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      ∏ i, (1 - 2 * hA.eigenvalues i * t) ^ (-(1 : ℝ) / 2) := by
  classical
  let b := hA.eigenvectorBasis
  have hc := gaussian_pi_sq_mgf (fun i => t * hA.eigenvalues i) (fun i => by
    convert ht i using 1 <;> ring)
  have hrepr : ∀ x : Fin n → ℝ,
      exp (t * ((∑ i, x i • b i : EuclideanSpace ℝ (Fin n)) ⬝ᵥ
        (A *ᵥ (∑ i, x i • b i : EuclideanSpace ℝ (Fin n))))) =
        exp (∑ i, (t * hA.eigenvalues i) * x i ^ 2) := by
    intro x
    rw [quadratic_spectral A hA, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hx : (∑ j, x j • b j) = b.repr.symm (WithLp.toLp 2 x) := b.sum_repr_symm _
    rw [hx, LinearIsometryEquiv.apply_symm_apply]
    ring
  have hm : Measurable (fun x : Fin n → ℝ => ∑ i, x i • b i) :=
    Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).smul measurable_const)
  have he : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      exp (t * (x ⬝ᵥ (A *ᵥ x)))) (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x : EuclideanSpace ℝ (Fin n), exp (t * (x ⬝ᵥ (A *ᵥ x)))
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
        ∏ i, (1 - 2 * hA.eigenvalues i * t) ^ (-(1 : ℝ) / 2) := by
    rw [stdGaussian_eq_map_pi_orthonormalBasis b]
    refine ⟨?_, ?_⟩
    · rw [integrable_map_measure (by fun_prop) hm.aemeasurable]
      simpa only [Function.comp_def, hrepr] using hc.1
    · rw [integral_map hm.aemeasurable (by fun_prop)]
      simp only [hrepr]
      have hd : ∀ i, 1 - 2 * (t * hA.eigenvalues i) = 1 - 2 * hA.eigenvalues i * t := by
        intro i
        ring
      simpa only [hd] using hc.2
  rw [← map_pi_eq_stdGaussian (ι := Fin n)] at he
  have hi := (integrable_map_measure (by fun_prop) (by fun_prop)).mp he.1
  have hval := he.2
  rw [integral_map (by fun_prop) (by fun_prop)] at hval
  exact ⟨hi, hval⟩

lemma repeated_sample_mgf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (M : ℕ) (hM : 0 < M) (t : ℝ)
    (ht : ∀ i, 2 * hA.eigenvalues i * t < 1) :
    Integrable (fun ω => exp (t * ((M : ℝ) * TraceEstimation.Shared.gaussianEstimator A M ω)))
      (TraceEstimation.Shared.gaussianSampleMeasure n M) ∧
    mgf (fun ω => (M : ℝ) * TraceEstimation.Shared.gaussianEstimator A M ω)
      (TraceEstimation.Shared.gaussianSampleMeasure n M) t =
      ∏ i, (1 - 2 * hA.eigenvalues i * t) ^ (-(M : ℝ) / 2) := by
  classical
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have he : ∀ ω : Fin M → Fin n → ℝ,
      t * ((M : ℝ) * TraceEstimation.Shared.gaussianEstimator A M ω) =
        ∑ j, t * (ω j ⬝ᵥ (A *ᵥ ω j)) := by
    intro ω
    simp only [TraceEstimation.Shared.gaussianEstimator, ← mul_assoc, mul_inv_cancel₀ hM0,
      one_mul, Finset.mul_sum]
  have hs := single_sample_mgf A hA t ht
  refine ⟨?_, ?_⟩
  · unfold TraceEstimation.Shared.gaussianSampleMeasure
    simp_rw [he, exp_sum]
    exact Integrable.fintype_prod_dep (fun _ : Fin M => hs.1)
  · unfold mgf TraceEstimation.Shared.gaussianSampleMeasure
    simp_rw [he, exp_sum]
    rw [integral_fintype_prod_eq_prod
      (fun (_ : Fin M) (x : Fin n → ℝ) => exp (t * (x ⬝ᵥ (A *ᵥ x))))]
    simp_rw [hs.2]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    have hp : 0 ≤ 1 - 2 * hA.eigenvalues i * t := by linarith [ht i]
    rw [← rpow_mul_natCast hp]
    congr 1
    ring

end TraceGaussianProof


open MeasureTheory ProbabilityTheory Real Matrix

namespace TraceGaussianProof

lemma gaussian_centered_factor_bound {a : ℝ} (ha : |a| ≤ 1 / 4) :
    exp (-a) * (1 - 2 * a) ^ (-(1 : ℝ) / 2) ≤ exp (4 * a ^ 2) := by
  have ha' : a ≤ 1 / 4 := (le_abs_self a).trans ha
  have hd : 0 < 1 - 2 * a := by linarith
  have hd' : 1 / 2 ≤ 1 - 2 * a := by linarith
  have hinv : (1 - 2 * a)⁻¹ ≤ 2 := by
    have h := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num)
      (show (0 : ℝ) < 1 / 2 by norm_num) hd'
    norm_num at h
    exact h
  have hl := one_sub_inv_le_log_of_pos hd
  have hc : -a + log (1 - 2 * a) * (-(1 : ℝ) / 2) ≤ 4 * a ^ 2 := by
    calc _ ≤ -a - (1 - (1 - 2 * a)⁻¹) / 2 := by linarith
      _ = 2 * a ^ 2 * (1 - 2 * a)⁻¹ := by
        rw [← div_eq_mul_inv]
        apply (eq_div_iff hd.ne').mpr
        nlinarith only [inv_mul_cancel₀ hd.ne']
      _ ≤ 2 * a ^ 2 * 2 := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 4 * a ^ 2 := by ring
  rw [rpow_def_of_pos hd, ← exp_add]
  exact exp_le_exp.mpr hc

lemma single_centered_mgf_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (s : ℝ) (hs : |s| * A.trace ≤ 1 / 4) :
    Integrable (fun x : Fin n → ℝ => exp (s * (x ⬝ᵥ (A *ᵥ x) - A.trace)))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) ∧
    (∫ x : Fin n → ℝ, exp (s * (x ⬝ᵥ (A *ᵥ x) - A.trace))
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) ≤ exp (4 * s ^ 2 * A.trace ^ 2) := by
  classical
  have hlam := hA.eigenvalues_nonneg
  have hsum : (∑ i, hA.1.eigenvalues i) = A.trace := hA.1.trace_eq_sum_eigenvalues.symm
  have hle : ∀ i, hA.1.eigenvalues i ≤ A.trace := by
    intro i
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hlam j) (Finset.mem_univ i)
  have ha : ∀ i, |s * hA.1.eigenvalues i| ≤ 1 / 4 := by
    intro i
    rw [abs_mul, abs_of_nonneg (hlam i)]
    exact (mul_le_mul_of_nonneg_left (hle i) (abs_nonneg s)).trans hs
  have hdom : ∀ i, 2 * hA.1.eigenvalues i * s < 1 := by
    intro i
    have := (le_abs_self (s * hA.1.eigenvalues i)).trans (ha i)
    nlinarith
  have hbase := single_sample_mgf A hA.1 s hdom
  have he : ∀ x : Fin n → ℝ,
      exp (s * (x ⬝ᵥ (A *ᵥ x) - A.trace)) =
        exp (-s * A.trace) * exp (s * (x ⬝ᵥ (A *ᵥ x))) := by
    intro x
    rw [← exp_add]
    congr 1
    ring
  have hprod : exp (-s * A.trace) = ∏ i, exp (-(s * hA.1.eigenvalues i)) := by
    rw [← exp_sum, Finset.sum_neg_distrib, ← Finset.mul_sum, hsum]
    congr 1
    ring
  refine ⟨?_, ?_⟩
  · simp_rw [he]
    exact hbase.1.const_mul _
  · simp_rw [he]
    rw [integral_const_mul, hbase.2, hprod, ← Finset.prod_mul_distrib]
    calc (∏ i, exp (-(s * hA.1.eigenvalues i)) *
            (1 - 2 * hA.1.eigenvalues i * s) ^ (-(1 : ℝ) / 2))
        ≤ ∏ i, exp (4 * (s * hA.1.eigenvalues i) ^ 2) := by
          apply Finset.prod_le_prod
          · intro i _
            exact mul_nonneg (exp_pos _).le (rpow_nonneg (by linarith [hdom i]) _)
          · intro i _
            have heq : 1 - 2 * (s * hA.1.eigenvalues i) =
                1 - 2 * hA.1.eigenvalues i * s := by ring
            simpa only [heq] using gaussian_centered_factor_bound (ha i)
      _ = exp (4 * s ^ 2 * ∑ i, hA.1.eigenvalues i ^ 2) := by
          rw [← exp_sum]
          congr 1
          simp_rw [mul_pow]
          rw [← Finset.mul_sum, ← Finset.mul_sum]
          ring
      _ ≤ exp (4 * s ^ 2 * A.trace ^ 2) := by
          apply exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← hsum]
          exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hlam i)

lemma repeated_centered_mgf_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (M : ℕ) (hM : 0 < M) (s : ℝ) (hs : |s| * A.trace ≤ 1 / 4) :
    Integrable (fun ω => exp (s * ((M : ℝ) * TraceEstimation.Shared.gaussianEstimator A M ω -
        (M : ℝ) * A.trace))) (TraceEstimation.Shared.gaussianSampleMeasure n M) ∧
    (∫ ω, exp (s * ((M : ℝ) * TraceEstimation.Shared.gaussianEstimator A M ω -
        (M : ℝ) * A.trace)) ∂TraceEstimation.Shared.gaussianSampleMeasure n M) ≤
      exp (4 * (M : ℝ) * s ^ 2 * A.trace ^ 2) := by
  classical
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have he : ∀ ω : Fin M → Fin n → ℝ,
      s * ((M : ℝ) * TraceEstimation.Shared.gaussianEstimator A M ω - (M : ℝ) * A.trace) =
        ∑ j, s * (ω j ⬝ᵥ (A *ᵥ ω j) - A.trace) := by
    intro ω
    simp only [TraceEstimation.Shared.gaussianEstimator, ← mul_assoc, mul_inv_cancel₀ hM0,
      one_mul, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hc := single_centered_mgf_bound A hA s hs
  refine ⟨?_, ?_⟩
  · unfold TraceEstimation.Shared.gaussianSampleMeasure
    simp_rw [he, exp_sum]
    exact Integrable.fintype_prod_dep (fun _ : Fin M => hc.1)
  · unfold TraceEstimation.Shared.gaussianSampleMeasure
    simp_rw [he, exp_sum]
    rw [integral_fintype_prod_eq_prod
      (fun (_ : Fin M) (x : Fin n → ℝ) => exp (s * (x ⬝ᵥ (A *ᵥ x) - A.trace)))]
    calc (∏ _ : Fin M, ∫ x : Fin n → ℝ, exp (s * (x ⬝ᵥ (A *ᵥ x) - A.trace))
          ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        ≤ ∏ _ : Fin M, exp (4 * s ^ 2 * A.trace ^ 2) :=
          Finset.prod_le_prod (fun _ _ => integral_nonneg (fun _ => (exp_pos _).le))
            (fun _ _ => hc.2)
      _ = exp (4 * (M : ℝ) * s ^ 2 * A.trace ^ 2) := by
        rw [← exp_sum]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        congr 1
        ring

end TraceGaussianProof


open MeasureTheory ProbabilityTheory Real Matrix

namespace TraceGaussianProof

lemma chernoff_parameter {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (Z : Ω → ℝ) (s u b : ℝ) (hs : 0 ≤ s)
    (hi : Integrable (fun ω => exp (s * Z ω)) P)
    (hb : mgf Z P s ≤ exp b) :
    P.real {ω | u ≤ Z ω} ≤ exp (-s * u + b) := by
  calc P.real {ω | u ≤ Z ω} ≤ exp (-s * u) * mgf Z P s :=
      measure_ge_le_exp_mul_mgf u hs hi
    _ ≤ exp (-s * u) * exp b := mul_le_mul_of_nonneg_left hb (exp_pos _).le
    _ = exp (-s * u + b) := (exp_add _ _).symm

lemma trace_tail_bounds {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (htr : 0 < A.trace) (M : ℕ) (hM : 0 < M) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10) :
    (TraceEstimation.Shared.gaussianSampleMeasure n M).real
        {ω | A.trace * (1 + ε) ≤ TraceEstimation.Shared.gaussianEstimator A M ω} ≤
      exp (-(M : ℝ) * ε ^ 2 / 20) ∧
    (TraceEstimation.Shared.gaussianSampleMeasure n M).real
        {ω | TraceEstimation.Shared.gaussianEstimator A M ω ≤ A.trace * (1 - ε)} ≤
      exp (-(M : ℝ) * ε ^ 2 / 20) := by
  let P := TraceEstimation.Shared.gaussianSampleMeasure n M
  haveI : IsProbabilityMeasure P := by
    dsimp [P, TraceEstimation.Shared.gaussianSampleMeasure]
    infer_instance
  let Z := fun ω => (M : ℝ) * TraceEstimation.Shared.gaussianEstimator A M ω - (M : ℝ) * A.trace
  let s := ε / (8 * A.trace)
  let u := (M : ℝ) * ε * A.trace
  have hs : 0 < s := by dsimp [s]; positivity
  have hst : s * A.trace = ε / 8 := by dsimp [s]; field_simp [htr.ne']
  have hsmall : |s| * A.trace ≤ 1 / 4 := by rw [abs_of_pos hs, hst]; linarith
  have hp := repeated_centered_mgf_bound A hA M hM s hsmall
  have hn := repeated_centered_mgf_bound A hA M hM (-s) (by simpa only [abs_neg] using hsmall)
  have hc : -s * u + 4 * (M : ℝ) * s ^ 2 * A.trace ^ 2 = -(M : ℝ) * ε ^ 2 / 16 := by
    dsimp [s, u]
    field_simp [htr.ne']
    ring
  have hcost : -s * u + 4 * (M : ℝ) * s ^ 2 * A.trace ^ 2 ≤ -(M : ℝ) * ε ^ 2 / 20 := by
    rw [hc]
    nlinarith [mul_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M) (sq_nonneg ε)]
  have hup : P.real {ω | u ≤ Z ω} ≤ exp (-(M : ℝ) * ε ^ 2 / 20) := by
    exact (chernoff_parameter P Z s u _ hs.le hp.1 hp.2).trans (exp_le_exp.mpr hcost)
  have hni : Integrable (fun ω => exp (s * (-Z ω))) P := by
    simpa only [Z, mul_neg, neg_mul] using hn.1
  have hnb : mgf (fun ω => -Z ω) P s ≤ exp (4 * (M : ℝ) * s ^ 2 * A.trace ^ 2) := by
    simpa only [mgf, Z, mul_neg, neg_mul, neg_sq] using hn.2
  have hlo : P.real {ω | u ≤ -Z ω} ≤ exp (-(M : ℝ) * ε ^ 2 / 20) :=
    (chernoff_parameter P (fun ω => -Z ω) s u _ hs.le hni hnb).trans (exp_le_exp.mpr hcost)
  refine ⟨(measureReal_mono ?_).trans hup, (measureReal_mono ?_).trans hlo⟩
  · intro ω hω
    change A.trace * (1 + ε) ≤ TraceEstimation.Shared.gaussianEstimator A M ω at hω
    have hh := mul_le_mul_of_nonneg_left hω (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
    change u ≤ Z ω
    dsimp [u, Z]
    nlinarith
  · intro ω hω
    change TraceEstimation.Shared.gaussianEstimator A M ω ≤ A.trace * (1 - ε) at hω
    have hh := mul_le_mul_of_nonneg_left hω (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
    change u ≤ -Z ω
    dsimp [u, Z]
    nlinarith

lemma sample_exponential_bound (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (M : ℕ) (hMbound : 20 * ε⁻¹ ^ 2 * log (2 / δ) ≤ (M : ℝ)) :
    exp (-(M : ℝ) * ε ^ 2 / 20) ≤ δ / 2 := by
  have hb := mul_le_mul_of_nonneg_right hMbound (sq_nonneg ε)
  have he : (20 * ε⁻¹ ^ 2 * log (2 / δ)) * ε ^ 2 = 20 * log (2 / δ) := by
    field_simp [hε.ne']
  rw [he] at hb
  have hc : -(M : ℝ) * ε ^ 2 / 20 ≤ log (δ / 2) := by
    have hl : log (2 / δ) = -log (δ / 2) := by
      rw [log_div (by norm_num) hδ.ne', log_div hδ.ne' (by norm_num)]
      ring
    rw [hl] at hb
    linarith
  calc exp (-(M : ℝ) * ε ^ 2 / 20) ≤ exp (log (δ / 2)) := exp_le_exp.mpr hc
    _ = δ / 2 := exp_log (by positivity)

lemma trace_two_tails {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (htr : 0 < A.trace) (ε δ : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1)
    (M : ℕ) (hM : 0 < M) (hMbound : 20 * ε⁻¹ ^ 2 * log (2 / δ) ≤ (M : ℝ)) :
    (TraceEstimation.Shared.gaussianSampleMeasure n M).real
        {ω | A.trace * (1 + ε) ≤ TraceEstimation.Shared.gaussianEstimator A M ω} ≤ δ / 2 ∧
    (TraceEstimation.Shared.gaussianSampleMeasure n M).real
        {ω | TraceEstimation.Shared.gaussianEstimator A M ω ≤ A.trace * (1 - ε)} ≤ δ / 2 := by
  have hs := sample_exponential_bound ε δ hε hδ M hMbound
  have ht := trace_tail_bounds A hA htr M hM ε hε hε'
  exact ⟨ht.1.trans hs, ht.2.trans hs⟩

end TraceGaussianProof

open TraceEstimation
open MeasureTheory ProbabilityTheory Real Matrix

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (htr : 0 < A.trace) (ε δ : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1)
    (M : ℕ) (hM : 0 < M) (hMbound : 20 * ε⁻¹ ^ 2 * Real.log (2 / δ) ≤ (M : ℝ)) :
    (Shared.gaussianSampleMeasure n M).real {ω | A.trace * (1 + ε) ≤ Shared.gaussianEstimator A M ω} ≤
      δ / 2 ∧
    (Shared.gaussianSampleMeasure n M).real {ω | Shared.gaussianEstimator A M ω ≤ A.trace * (1 - ε)} ≤
      δ / 2 := by
  exact TraceGaussianProof.trace_two_tails A hA htr ε δ hε hε' hδ hδ' M hM hMbound
