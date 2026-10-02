-- Prove2me | solution 1 for TraceEstimation.Gaussian.mgf_formula
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-01T19:07:10.947981+00:00
-- url     : https://prove2.me/submissions/19c31601-1206-4ad7-81ac-c9e6fd3b2268

import Mathlib
import Definitions.Def_TraceEstimation_Shared_gaussianEstimator
import Definitions.Def_TraceEstimation_Gaussian_hPoly


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


open Real

namespace TraceGaussianProof

lemma product_expansion {n : ℕ} (lam : Fin n → ℝ) (t : ℝ) :
    (∏ i, (1 - 2 * lam i * t)) =
      1 - 2 * (∑ i, lam i) * t + TraceEstimation.Gaussian.hPoly lam t := by
  classical
  let E : ℕ → ℝ := fun k => (-2 : ℝ) ^ k * t ^ k *
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ i ∈ S, lam i
  have hterm : ∀ k : ℕ,
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        ∏ i ∈ S, ((-2 : ℝ) * t) * lam i) = E k := by
    intro k
    dsimp [E]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    rw [Finset.prod_mul_distrib, Finset.prod_const,
      (Finset.mem_powersetCard.mp hS).2, mul_pow]
  have hraw : (∏ i, (1 - 2 * lam i * t)) = ∑ k ∈ Finset.range (n + 1), E k := by
    calc
      _ = (∏ i, (1 + ((-2 : ℝ) * t) * lam i)) := by
        apply Finset.prod_congr rfl
        intro i _
        congr 1
        ring
      _ = (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          ∏ i ∈ S, ((-2 : ℝ) * t) * lam i) := Finset.prod_one_add _
      _ = (∑ k ∈ Finset.range (n + 1), E k) := by
        rw [Finset.sum_powerset]
        simpa only [Finset.card_univ, Fintype.card_fin, hterm]
  cases n with
  | zero => simp [TraceEstimation.Gaussian.hPoly]
  | succ n =>
    have h0 : E 0 = 1 := by simp [E]
    have h1 : E 1 = (-2 * t) * ∑ i, lam i := by
      simp [E, Finset.powersetCard_one]
    have hrange : Finset.range (n + 1 + 1) =
        insert 0 (insert 1 (Finset.Icc 2 (n + 1))) := by
      ext k
      simp
      omega
    rw [hraw]
    change (∑ k ∈ Finset.range (n + 1 + 1), E k) = _
    rw [hrange, Finset.sum_insert (by simp), Finset.sum_insert (by simp), h0, h1]
    change 1 + ((-2 * t) * (∑ i, lam i) + TraceEstimation.Gaussian.hPoly lam t) = _
    ring

end TraceGaussianProof


open MeasureTheory ProbabilityTheory Real Matrix

namespace TraceGaussianProof

theorem trace_mgf_formula {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (M : ℕ) (hM : 0 < M) (t : ℝ) (ht : ∀ i, 2 * hA.eigenvalues i * t < 1) :
    mgf (fun ω => (M : ℝ) * TraceEstimation.Shared.gaussianEstimator A M ω)
      (TraceEstimation.Shared.gaussianSampleMeasure n M) t =
        ∏ i, (1 - 2 * hA.eigenvalues i * t) ^ (-(M : ℝ) / 2) ∧
    mgf (fun ω => (M : ℝ) * TraceEstimation.Shared.gaussianEstimator A M ω)
      (TraceEstimation.Shared.gaussianSampleMeasure n M) t =
        (1 - 2 * A.trace * t + TraceEstimation.Gaussian.hPoly hA.eigenvalues t) ^
          (-(M : ℝ) / 2) := by
  have hs := (repeated_sample_mgf A hA M hM t ht).2
  refine ⟨hs, hs.trans ?_⟩
  rw [Real.finsetProd_rpow _ _ (fun i _ => by linarith [ht i])]
  rw [product_expansion]
  congr 1
  rw [hA.trace_eq_sum_eigenvalues]
  rfl

end TraceGaussianProof


open TraceEstimation TraceEstimation.Gaussian
open MeasureTheory ProbabilityTheory Matrix

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (M : ℕ) (hM : 0 < M) (t : ℝ) (ht : ∀ i, 2 * hA.eigenvalues i * t < 1) :
    mgf (fun ω => (M : ℝ) * Shared.gaussianEstimator A M ω) (Shared.gaussianSampleMeasure n M) t =
      ∏ i : Fin n, (1 - 2 * hA.eigenvalues i * t) ^ (-(M : ℝ) / 2) ∧
    mgf (fun ω => (M : ℝ) * Shared.gaussianEstimator A M ω) (Shared.gaussianSampleMeasure n M) t =
      (1 - 2 * A.trace * t + hPoly hA.eigenvalues t) ^ (-(M : ℝ) / 2)  := by
  exact TraceGaussianProof.trace_mgf_formula A hA M hM t ht
