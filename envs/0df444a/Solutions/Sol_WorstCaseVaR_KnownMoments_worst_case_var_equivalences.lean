-- Prove2me | solution 1 for WorstCaseVaR.KnownMoments.worst_case_var_equivalences
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-05T01:08:53.770673+00:00
-- url     : https://prove2.me/submissions/9c55d679-3f42-4695-8faf-0a1e92b6a641

import Mathlib
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic

open MeasureTheory Matrix
open scoped InnerProductSpace

set_option autoImplicit false


/- Inlined checked module: GaussianMomentBridge -/
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

theorem gaussian_coordinate_memLp {n : ℕ} (μ : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 (multivariateGaussian μ S) := by
  have h : (fun x : EuclideanSpace ℝ (Fin n) => x i) =
      fun x => ⟪EuclideanSpace.basisFun (Fin n) ℝ i, x⟫_ℝ := by
    funext x
    simp [PiLp.inner_apply]
  rw [h]
  exact IsGaussian.memLp_two_id.const_inner _

theorem gaussian_coordinate_mean {n : ℕ} (μ : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (∫ x : EuclideanSpace ℝ (Fin n), x i ∂multivariateGaussian μ S) = μ i := by
  have h : (fun x : EuclideanSpace ℝ (Fin n) => x i) =
      fun x => ⟪EuclideanSpace.basisFun (Fin n) ℝ i, x⟫_ℝ := by
    funext x
    simp [PiLp.inner_apply]
  rw [h, integral_inner IsGaussian.integrable_fun_id, integral_id_multivariateGaussian]
  simp [PiLp.inner_apply]

/-- The canonical moment predicate is realized even for a singular positive semidefinite covariance. -/
theorem gaussian_hasMeanCov {n : ℕ} (μ : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) :
    HasMeanCov (multivariateGaussian μ S) μ S := by
  refine ⟨inferInstance, gaussian_coordinate_memLp μ S, gaussian_coordinate_mean μ S, ?_⟩
  intro i j
  have h := covariance_eval_multivariateGaussian (μ := μ) hS i j
  simpa only [covariance, gaussian_coordinate_mean] using h

end WorstCaseVaR.KnownMoments
end


/- Inlined checked module: LinearMoments -/
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

def linearForm {n : ℕ} (w : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ := w ⬝ᵥ ⇑x

theorem HasMeanCov.memLp_linear {n : ℕ} {P : Measure (EuclideanSpace ℝ (Fin n))}
    {μ : EuclideanSpace ℝ (Fin n)} {S : Matrix (Fin n) (Fin n) ℝ}
    (h : HasMeanCov P μ S) (w : Fin n → ℝ) : MemLp (linearForm w) 2 P := by
  exact memLp_finsetSum Finset.univ (fun i _ => (h.memLp_two i).const_mul (w i))

theorem HasMeanCov.mean_linear {n : ℕ} {P : Measure (EuclideanSpace ℝ (Fin n))}
    {μ : EuclideanSpace ℝ (Fin n)} {S : Matrix (Fin n) (Fin n) ℝ}
    (h : HasMeanCov P μ S) (w : Fin n → ℝ) : (∫ x, linearForm w x ∂P) = w ⬝ᵥ ⇑μ := by
  have : IsProbabilityMeasure P := h.isProbabilityMeasure
  unfold linearForm dotProduct
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, h.mean_eq]
  · intro i _
    exact ((h.memLp_two i).const_mul (w i)).integrable (by norm_num)

theorem HasMeanCov.cov_coordinate {n : ℕ} {P : Measure (EuclideanSpace ℝ (Fin n))}
    {μ : EuclideanSpace ℝ (Fin n)} {S : Matrix (Fin n) (Fin n) ℝ}
    (h : HasMeanCov P μ S) (i j : Fin n) :
    covariance (fun x : EuclideanSpace ℝ (Fin n) => x i) (fun x => x j) P = S i j := by
  simpa only [covariance, h.mean_eq] using h.cov_eq i j

theorem HasMeanCov.cov_linear {n : ℕ} {P : Measure (EuclideanSpace ℝ (Fin n))}
    {μ : EuclideanSpace ℝ (Fin n)} {S : Matrix (Fin n) (Fin n) ℝ}
    (h : HasMeanCov P μ S) (w z : Fin n → ℝ) :
    covariance (linearForm w) (linearForm z) P = w ⬝ᵥ (S *ᵥ z) := by
  have : IsProbabilityMeasure P := h.isProbabilityMeasure
  unfold linearForm dotProduct
  rw [covariance_fun_sum_fun_sum]
  · simp_rw [covariance_const_mul_left, covariance_const_mul_right, h.cov_coordinate]
    simp only [mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · exact fun i => (h.memLp_two i).const_mul (w i)
  · exact fun i => (h.memLp_two i).const_mul (z i)

theorem HasMeanCov.variance_linear {n : ℕ} {P : Measure (EuclideanSpace ℝ (Fin n))}
    {μ : EuclideanSpace ℝ (Fin n)} {S : Matrix (Fin n) (Fin n) ℝ}
    (h : HasMeanCov P μ S) (w : Fin n → ℝ) :
    Var[linearForm w; P] = w ⬝ᵥ (S *ᵥ w) := by
  rw [← covariance_self (h.memLp_linear w).aemeasurable]
  exact h.cov_linear w w

end WorstCaseVaR.KnownMoments
end


/- Inlined checked module: SharpTailBound -/
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace WorstCaseVaR.KnownMoments

/-- The one-sided second-moment bound with its exact denominator, for the closed tail event. -/
theorem sharp_tail_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : MemLp X 2 P)
    (m v t : ℝ) (hm : (∫ ω, X ω ∂P) = m)
    (hv : (∫ ω, (X ω - m) ^ 2 ∂P) = v) (hv0 : 0 < v) (ht : 0 < t) :
    P {ω | m + t ≤ X ω} ≤ ENNReal.ofReal (v / (v + t ^ 2)) := by
  let a := v / t
  have ha : 0 ≤ a := div_nonneg hv0.le ht.le
  have hta : 0 < t + a := by linarith
  have hcenter : MemLp (fun ω => X ω - m) 2 P := hX.sub (memLp_const _)
  have hcenter_int : Integrable (fun ω => X ω - m) P := hcenter.integrable (by norm_num)
  have hmean : (∫ ω, (X ω - m) ∂P) = 0 := by
    rw [integral_sub (hX.integrable (by norm_num)) (integrable_const _), hm]
    simp
  have hsquare : Integrable (fun ω => (X ω - m + a) ^ 2) P :=
    (hcenter.add (memLp_const _)).integrable_sq
  have hexpand : (fun ω => (X ω - m + a) ^ 2) =
      fun ω => ((X ω - m) ^ 2 + (2 * a) * (X ω - m)) + a ^ 2 := by
    funext ω
    ring
  have hintegral : (∫ ω, (X ω - m + a) ^ 2 ∂P) = v + a ^ 2 := by
    have hi : Integrable (fun ω => (2 * a) * (X ω - m)) P := hcenter_int.const_mul (2 * a)
    have hi' : Integrable (fun ω => (X ω - m) ^ 2 + (2 * a) * (X ω - m)) P :=
      hcenter.integrable_sq.add hi
    rw [hexpand, integral_add hi' (integrable_const (a ^ 2)),
      integral_add hcenter.integrable_sq hi,
      integral_const_mul, hmean, hv]
    simp
  have hsub : {ω | m + t ≤ X ω} ⊆ {ω | (t + a) ^ 2 ≤ (X ω - m + a) ^ 2} := by
    intro ω hω
    change m + t ≤ X ω at hω
    change (t + a) ^ 2 ≤ (X ω - m + a) ^ 2
    have hx : t + a ≤ X ω - m + a := by linarith [hω]
    exact pow_le_pow_left₀ hta.le hx 2
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := P) (f := fun ω => (X ω - m + a) ^ 2) (ae_of_all _ (fun _ => sq_nonneg _))
      hsquare ((t + a) ^ 2)
  rw [hintegral] at hmarkov
  have hreal : P.real {ω | m + t ≤ X ω} ≤ (v + a ^ 2) / (t + a) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hta)).2
    calc
      P.real {ω | m + t ≤ X ω} * (t + a) ^ 2 ≤
          P.real {ω | (t + a) ^ 2 ≤ (X ω - m + a) ^ 2} * (t + a) ^ 2 :=
        mul_le_mul_of_nonneg_right (measureReal_mono hsub) (sq_nonneg _)
      _ ≤ v + a ^ 2 := by simpa only [mul_comm] using hmarkov
  have hden : 0 < v + t ^ 2 := by positivity
  have hratio : (v + a ^ 2) / (t + a) ^ 2 = v / (v + t ^ 2) := by
    dsimp [a]
    field_simp
    ring
  rw [hratio] at hreal
  apply (ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (div_nonneg hv0.le hden.le)]
  exact hreal

end WorstCaseVaR.KnownMoments
end


/- Inlined checked module: ResidualCovariance -/
section
set_option autoImplicit false

open Matrix

namespace WorstCaseVaR.KnownMoments

def portfolioVariance {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) : ℝ :=
  w ⬝ᵥ (S *ᵥ w)

noncomputable def residualCovariance {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  S - (1 / portfolioVariance S w) • vecMulVec (S *ᵥ w) (S *ᵥ w)

theorem portfolioVariance_pos {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.PosDef) {w : Fin n → ℝ} (hw : w ≠ 0) : 0 < portfolioVariance S w := by
  simpa only [portfolioVariance, star_trivial] using hS.dotProduct_mulVec_pos hw

theorem symmetric_pairing {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.IsHermitian) (x y : Fin n → ℝ) : x ⬝ᵥ (S *ᵥ y) = y ⬝ᵥ (S *ᵥ x) := by
  have hs : Sᵀ = S := isHermitian_iff_isSymm.mp hS
  simpa only [hs] using dotProduct_transpose_mulVec S x y

theorem outer_quadratic {n : ℕ} (x d : Fin n → ℝ) :
    x ⬝ᵥ (vecMulVec d d *ᵥ x) = (x ⬝ᵥ d) ^ 2 := by
  simp [vecMulVec_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_comm, pow_two]

theorem residual_quadratic {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (w x : Fin n → ℝ) :
    x ⬝ᵥ (residualCovariance S w *ᵥ x) =
      x ⬝ᵥ (S *ᵥ x) - (x ⬝ᵥ (S *ᵥ w)) ^ 2 / portfolioVariance S w := by
  simp only [residualCovariance, sub_mulVec, smul_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul, outer_quadratic]
  ring

/-- Remove exactly the covariance in the portfolio direction; the residual remains PSD. -/
theorem residualCovariance_posSemidef {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.PosDef) {w : Fin n → ℝ} (hw : w ≠ 0) : (residualCovariance S w).PosSemidef := by
  let v := portfolioVariance S w
  have hv : 0 < v := portfolioVariance_pos hS hw
  have hd : (vecMulVec (S *ᵥ w) (S *ᵥ w)).PosSemidef := by
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star (S *ᵥ w)
  apply PosSemidef.of_dotProduct_mulVec_nonneg
    (hS.isHermitian.sub (hd.isHermitian.smul (by rfl)))
  intro x
  change 0 ≤ x ⬝ᵥ (residualCovariance S w *ᵥ x)
  rw [residual_quadratic]
  have h := hS.posSemidef.dotProduct_mulVec_nonneg (x - ((x ⬝ᵥ (S *ᵥ w)) / v) • w)
  simp only [star_trivial, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, symmetric_pairing hS.isHermitian w x] at h
  change 0 ≤ x ⬝ᵥ (S *ᵥ x) - (x ⬝ᵥ (S *ᵥ w)) ^ 2 / v
  have heq : (x ⬝ᵥ (S *ᵥ x) - (x ⬝ᵥ (S *ᵥ w)) / v * (x ⬝ᵥ (S *ᵥ w))) -
      (x ⬝ᵥ (S *ᵥ w)) / v * ((x ⬝ᵥ (S *ᵥ w)) -
        (x ⬝ᵥ (S *ᵥ w)) / v * v) =
      x ⬝ᵥ (S *ᵥ x) - (x ⬝ᵥ (S *ᵥ w)) ^ 2 / v := by
    field_simp
    ring
  change 0 ≤ (x ⬝ᵥ (S *ᵥ x) - (x ⬝ᵥ (S *ᵥ w)) / v * (x ⬝ᵥ (S *ᵥ w))) -
      (x ⬝ᵥ (S *ᵥ w)) / v * ((x ⬝ᵥ (S *ᵥ w)) -
        (x ⬝ᵥ (S *ᵥ w)) / v * v) at h
  rwa [heq] at h

theorem residual_variance_zero {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.PosDef) {w : Fin n → ℝ} (hw : w ≠ 0) :
    w ⬝ᵥ (residualCovariance S w *ᵥ w) = 0 := by
  rw [residual_quadratic]
  have hv := portfolioVariance_pos hS hw
  change portfolioVariance S w - portfolioVariance S w ^ 2 / portfolioVariance S w = 0
  field_simp
  ring

end WorstCaseVaR.KnownMoments
end


/- Inlined checked module: MixtureMoments -/
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

noncomputable def mixture {Ω : Type*} [MeasurableSpace Ω] (p q : ℝ)
    (P Q : Measure Ω) : Measure Ω := ENNReal.ofReal p • P + ENNReal.ofReal q • Q

theorem mixture_probability {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) : IsProbabilityMeasure (mixture p q P Q) := by
  constructor
  simp only [mixture, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp hq, hpq]
  simp

theorem mixture_integral {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω)
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (f : Ω → ℝ)
    (hP : Integrable f P) (hQ : Integrable f Q) :
    (∫ x, f x ∂mixture p q P Q) = p * (∫ x, f x ∂P) + q * (∫ x, f x ∂Q) := by
  rw [mixture, integral_add_measure (hP.smul_measure ENNReal.ofReal_ne_top)
    (hQ.smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq,
    smul_eq_mul]

theorem HasMeanCov.raw_second {n : ℕ} {P : Measure (EuclideanSpace ℝ (Fin n))}
    {μ : EuclideanSpace ℝ (Fin n)} {S : Matrix (Fin n) (Fin n) ℝ}
    (h : HasMeanCov P μ S) (i j : Fin n) :
    (∫ x, x i * x j ∂P) = S i j + μ i * μ j := by
  have : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hc := covariance_eq_sub (h.memLp_two i) (h.memLp_two j)
  rw [h.cov_coordinate, h.mean_eq, h.mean_eq] at hc
  change S i j = (∫ x, x i * x j ∂P) - μ i * μ j at hc
  linarith

theorem mixture_memLp_coordinate {n : ℕ} {P Q : Measure (EuclideanSpace ℝ (Fin n))}
    {μ ν : EuclideanSpace ℝ (Fin n)} {S T : Matrix (Fin n) (Fin n) ℝ}
    (hP : HasMeanCov P μ S) (hQ : HasMeanCov Q ν T) (p q : ℝ) (i : Fin n) :
    MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 (mixture p q P Q) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  exact ((hP.memLp_two i).integrable_sq.smul_measure ENNReal.ofReal_ne_top).add_measure
    ((hQ.memLp_two i).integrable_sq.smul_measure ENNReal.ofReal_ne_top)

/-- The complete coordinate mean/covariance formula for a two-component mixture. -/
theorem mixture_hasMeanCov {n : ℕ} {P Q : Measure (EuclideanSpace ℝ (Fin n))}
    {μ ν : EuclideanSpace ℝ (Fin n)} {S T : Matrix (Fin n) (Fin n) ℝ}
    (hP : HasMeanCov P μ S) (hQ : HasMeanCov Q ν T) (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) :
    HasMeanCov (mixture p q P Q) (p • μ + q • ν)
      (fun i j => p * (S i j + μ i * μ j) + q * (T i j + ν i * ν j) -
        (p * μ i + q * ν i) * (p * μ j + q * ν j)) := by
  have : IsProbabilityMeasure P := hP.isProbabilityMeasure
  have : IsProbabilityMeasure Q := hQ.isProbabilityMeasure
  have hprob := mixture_probability P Q p q hp hq hpq
  have hmean (i : Fin n) : (∫ x, x i ∂mixture p q P Q) = p * μ i + q * ν i := by
    rw [mixture_integral P Q p q hp hq _ ((hP.memLp_two i).integrable (by norm_num))
      ((hQ.memLp_two i).integrable (by norm_num)), hP.mean_eq, hQ.mean_eq]
  refine ⟨hprob, mixture_memLp_coordinate hP hQ p q, ?_, ?_⟩
  · intro i
    simpa using hmean i
  · intro i j
    have hc := covariance_eq_sub (mixture_memLp_coordinate hP hQ p q i)
      (mixture_memLp_coordinate hP hQ p q j)
    simp only [covariance, hmean, Pi.mul_apply] at hc
    change (∫ x, (x i - (p * μ i + q * ν i)) * (x j - (p * μ j + q * ν j))
      ∂mixture p q P Q) = _
    have hmix := mixture_integral P Q p q hp hq
      (fun x : EuclideanSpace ℝ (Fin n) => x i * x j)
      ((hP.memLp_two i).integrable_mul (hP.memLp_two j))
      ((hQ.memLp_two i).integrable_mul (hQ.memLp_two j))
    rw [hc, hmix, hP.raw_second, hQ.raw_second]

end WorstCaseVaR.KnownMoments
end


/- Inlined checked module: SharpMeasure -/
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

noncomputable def upperMean {n : ℕ} (μ : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) (t : ℝ) : EuclideanSpace ℝ (Fin n) :=
  μ - (t / portfolioVariance S w) • WithLp.toLp 2 (S *ᵥ w)

noncomputable def lowerMean {n : ℕ} (μ : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) (t : ℝ) : EuclideanSpace ℝ (Fin n) :=
  μ + (1 / t) • WithLp.toLp 2 (S *ᵥ w)

noncomputable def sharpMeasure {n : ℕ} (μ : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) (t : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  let v := portfolioVariance S w
  mixture (v / (v + t ^ 2)) (t ^ 2 / (v + t ^ 2))
    (multivariateGaussian (upperMean μ S w t) (residualCovariance S w))
    (multivariateGaussian (lowerMean μ S w t) (residualCovariance S w))

/-- The sharp-tail witness preserves every coordinate mean and covariance. -/
theorem sharpMeasure_hasMeanCov {n : ℕ} (μ : EuclideanSpace ℝ (Fin n))
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) {w : Fin n → ℝ} (hw : w ≠ 0)
    (t : ℝ) (ht : 0 < t) : HasMeanCov (sharpMeasure μ S w t) μ S := by
  let v := portfolioVariance S w
  let p := v / (v + t ^ 2)
  let q := t ^ 2 / (v + t ^ 2)
  have hv : 0 < v := portfolioVariance_pos hS hw
  have hden : 0 < v + t ^ 2 := by positivity
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p + q = 1 := by dsimp [p, q]; rw [← add_div, div_self hden.ne']
  have hR := residualCovariance_posSemidef hS hw
  have h := mixture_hasMeanCov
    (gaussian_hasMeanCov (upperMean μ S w t) _ hR)
    (gaussian_hasMeanCov (lowerMean μ S w t) _ hR) p q hp hq hpq
  have hmean : p • upperMean μ S w t + q • lowerMean μ S w t = μ := by
    ext i
    simp only [upperMean, lowerMean, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]
    change p * (μ i - t / v * (S *ᵥ w) i) + q * (μ i + 1 / t * (S *ᵥ w) i) = μ i
    dsimp [p, q]
    field_simp
    ring
  have hcov : (fun i j => p * (residualCovariance S w i j + upperMean μ S w t i * upperMean μ S w t j) +
        q * (residualCovariance S w i j + lowerMean μ S w t i * lowerMean μ S w t j) -
        (p * upperMean μ S w t i + q * lowerMean μ S w t i) *
          (p * upperMean μ S w t j + q * lowerMean μ S w t j)) = S := by
    ext i j
    simp only [upperMean, lowerMean, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, residualCovariance, Matrix.sub_apply,
      Matrix.smul_apply, vecMulVec_apply]
    change p * (S i j - (1 / v) * ((S *ᵥ w) i * (S *ᵥ w) j) +
        (μ i - t / v * (S *ᵥ w) i) * (μ j - t / v * (S *ᵥ w) j)) +
      q * (S i j - (1 / v) * ((S *ᵥ w) i * (S *ᵥ w) j) +
        (μ i + 1 / t * (S *ᵥ w) i) * (μ j + 1 / t * (S *ᵥ w) j)) -
      (p * (μ i - t / v * (S *ᵥ w) i) + q * (μ i + 1 / t * (S *ᵥ w) i)) *
        (p * (μ j - t / v * (S *ᵥ w) j) + q * (μ j + 1 / t * (S *ᵥ w) j)) = S i j
    dsimp [p, q]
    field_simp
    ring
  rw [hmean, hcov] at h
  exact h

theorem upperMean_linear {n : ℕ} (μ : EuclideanSpace ℝ (Fin n))
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) {w : Fin n → ℝ} (hw : w ≠ 0) (t : ℝ) :
    linearForm w (upperMean μ S w t) = linearForm w μ - t := by
  change w ⬝ᵥ (⇑μ - (t / portfolioVariance S w) • (S *ᵥ w)) = w ⬝ᵥ ⇑μ - t
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hv := portfolioVariance_pos hS hw
  change w ⬝ᵥ ⇑μ - t / portfolioVariance S w * portfolioVariance S w = w ⬝ᵥ ⇑μ - t
  rw [div_mul_cancel₀ _ hv.ne']

/-- The upper component is supported on the exact desired loss hyperplane. -/
theorem upper_gaussian_loss_ae {n : ℕ} (μ : EuclideanSpace ℝ (Fin n))
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) {w : Fin n → ℝ} (hw : w ≠ 0) (t : ℝ) :
    ∀ᵐ x ∂multivariateGaussian (upperMean μ S w t) (residualCovariance S w),
      -linearForm w x = -linearForm w μ + t := by
  let P := multivariateGaussian (upperMean μ S w t) (residualCovariance S w)
  have hP := gaussian_hasMeanCov (upperMean μ S w t) _ (residualCovariance_posSemidef hS hw)
  have hz : Var[linearForm w; P] = 0 :=
    (hP.variance_linear w).trans (residual_variance_zero hS hw)
  have hae := ae_eq_integral_of_variance_eq_zero (hP.memLp_linear w) hz
  rw [hP.mean_linear] at hae
  have hm := upperMean_linear μ hS hw t
  filter_upwards [hae] with x hx
  change linearForm w x = linearForm w (upperMean μ S w t) at hx
  rw [hm] at hx
  linarith

end WorstCaseVaR.KnownMoments
end


/- Inlined checked module: TailThreshold -/
section
set_option autoImplicit false

namespace WorstCaseVaR.KnownMoments

theorem kappa_pos {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) : 0 < kappa ε :=
  Real.sqrt_pos.mpr (div_pos (sub_pos.mpr hε1) hε0)

theorem kappa_sq {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    kappa ε ^ 2 = (1 - ε) / ε :=
  Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hε1.le) hε0.le)

theorem tail_ratio_le_iff {v t ε : ℝ} (hv : 0 < v) (ht : 0 ≤ t)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    v / (v + t ^ 2) ≤ ε ↔ kappa ε * Real.sqrt v ≤ t := by
  have hden : 0 < v + t ^ 2 := by positivity
  have hk : 0 ≤ kappa ε * Real.sqrt v := mul_nonneg (kappa_pos hε0 hε1).le (Real.sqrt_nonneg _)
  rw [div_le_iff₀ hden, ← sq_le_sq₀ hk ht, mul_pow, kappa_sq hε0 hε1, Real.sq_sqrt hv.le]
  have heq : (1 - ε) / ε * v = ((1 - ε) * v) / ε := by ring
  rw [heq, div_le_iff₀ hε0]
  constructor <;> intro h <;> nlinarith

theorem tail_ratio_gt {v t ε : ℝ} (hv : 0 < v) (ht : 0 ≤ t)
    (hε0 : 0 < ε) (hε1 : ε < 1) (htop : t < kappa ε * Real.sqrt v) :
    ε < v / (v + t ^ 2) := by
  apply lt_of_not_ge
  intro h
  exact (not_le_of_gt htop) ((tail_ratio_le_iff hv ht hε0 hε1).mp h)

end WorstCaseVaR.KnownMoments
end


/- Inlined checked module: SharpMeasureProbability -/
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

theorem sharpMeasure_tail_lower {n : ℕ} (μ : EuclideanSpace ℝ (Fin n))
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) {w : Fin n → ℝ} (hw : w ≠ 0)
    (t γ : ℝ) (hγ : γ ≤ -linearForm w μ + t) :
    ENNReal.ofReal (portfolioVariance S w / (portfolioVariance S w + t ^ 2)) ≤
      sharpMeasure μ S w t {x | γ ≤ -linearForm w x} := by
  have hmeas : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | γ ≤ -linearForm w x} := by
    unfold linearForm dotProduct
    exact measurableSet_le measurable_const (by fun_prop)
  have hae : ∀ᵐ x ∂multivariateGaussian (upperMean μ S w t) (residualCovariance S w),
      γ ≤ -linearForm w x := by
    filter_upwards [upper_gaussian_loss_ae μ hS hw t] with x hx
    rw [hx]
    exact hγ
  have hmass := (mem_ae_iff_prob_eq_one hmeas).mp hae
  simp only [sharpMeasure, mixture, Measure.add_apply, Measure.smul_apply, hmass,
    smul_eq_mul, mul_one]
  exact le_self_add

theorem linearForm_eq_inner {n : ℕ} (w x : EuclideanSpace ℝ (Fin n)) :
    linearForm ⇑w x = ⟪w, x⟫_ℝ := by
  simp [linearForm, dotProduct, PiLp.inner_apply, mul_comm]

theorem coe_ne_zero {n : ℕ} {w : EuclideanSpace ℝ (Fin n)} (hw : w ≠ 0) :
    (⇑w : Fin n → ℝ) ≠ 0 := by
  intro h
  apply hw
  ext i
  exact congrFun h i

end WorstCaseVaR.KnownMoments
end


/- Inlined checked module: ProbabilityScalarEquivalence -/
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

theorem probability_iff_scalar {n : ℕ} (μ w : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) (hw : w ≠ 0)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (γ : ℝ) :
    (∀ P : Measure (EuclideanSpace ℝ (Fin n)), HasMeanCov P μ S →
      P (lossSet w γ) ≤ ENNReal.ofReal ε) ↔
    kappa ε * Real.sqrt (⇑w ⬝ᵥ S *ᵥ ⇑w) - ⟪μ, w⟫_ℝ ≤ γ := by
  let v := portfolioVariance S ⇑w
  have hw' := coe_ne_zero hw
  have hv : 0 < v := portfolioVariance_pos hS hw'
  have hmean_inner : linearForm ⇑w μ = ⟪μ, w⟫_ℝ := by
    rw [linearForm_eq_inner, real_inner_comm]
  have hk : 0 < kappa ε * Real.sqrt v := mul_pos (kappa_pos hε0 hε1) (Real.sqrt_pos.mpr hv)
  have hevent : lossSet w γ = {x | γ ≤ -linearForm ⇑w x} := by
    ext x
    simp only [lossSet, Set.mem_ofPred_eq, linearForm_eq_inner]
  constructor
  · intro hbound
    by_contra hscalar
    let δ := γ + linearForm ⇑w μ
    have hδ : δ < kappa ε * Real.sqrt v := by
      dsimp [δ, v, portfolioVariance]
      rw [hmean_inner]
      exact lt_of_not_ge (by intro h; exact hscalar (by linarith))
    obtain ⟨t, htlow, hthi⟩ := exists_between (max_lt hδ hk)
    have ht : 0 < t := lt_of_le_of_lt (le_max_right _ _) htlow
    have hγ : γ ≤ -linearForm ⇑w μ + t := by
      have hdt := lt_of_le_of_lt (le_max_left _ _) htlow
      dsimp [δ] at hdt
      linarith
    have hupper := hbound (sharpMeasure μ S ⇑w t) (sharpMeasure_hasMeanCov μ hS hw' t ht)
    rw [hevent] at hupper
    have hlower := sharpMeasure_tail_lower μ hS hw' t γ hγ
    have hr : v / (v + t ^ 2) ≤ ε := (ENNReal.ofReal_le_ofReal_iff hε0.le).mp
      (hlower.trans hupper)
    exact (not_le_of_gt (tail_ratio_gt hv ht.le hε0 hε1 hthi)) hr
  · intro hscalar P hP
    have : IsProbabilityMeasure P := hP.isProbabilityMeasure
    let X := fun x => -linearForm ⇑w x
    let m := -linearForm ⇑w μ
    let δ := γ - m
    have hδ : kappa ε * Real.sqrt v ≤ δ := by
      dsimp [δ, m, v, portfolioVariance]
      rw [hmean_inner]
      linarith
    have ht : 0 < δ := hk.trans_le hδ
    have hX : MemLp X 2 P := (hP.memLp_linear ⇑w).neg
    have hmean : (∫ x, X x ∂P) = m := by
      dsimp [X, m]
      rw [integral_neg, hP.mean_linear]
      rfl
    have hvar : Var[X; P] = v := by
      simpa only [X, v, portfolioVariance, variance_fun_neg] using hP.variance_linear ⇑w
    have hsecond : (∫ x, (X x - m) ^ 2 ∂P) = v := by
      have h := variance_eq_integral hX.aemeasurable
      rw [hmean] at h
      exact h.symm.trans hvar
    have htail := sharp_tail_bound P X hX m v δ hmean hsecond hv ht
    have hr := (tail_ratio_le_iff hv ht.le hε0 hε1).mpr hδ
    have hmd : m + δ = γ := by dsimp [δ]; ring
    have hset : {x | m + δ ≤ X x} = lossSet w γ := by
      rw [hmd, hevent]
    rw [hset] at htail
    exact htail.trans (ENNReal.ofReal_le_ofReal hr)

end WorstCaseVaR.KnownMoments
end


/- Inlined checked module: PSDTrace -/
section
set_option autoImplicit false

open Matrix
open scoped MatrixOrder

namespace WorstCaseVaR.KnownMoments

theorem psd_trace_product_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [star_eq_conjTranspose, trace_mul_cycle, trace_mul_cycle]
  exact (hB.mul_mul_conjTranspose_same C).trace_nonneg

/-- Positive definite second moments make zero expected nonnegative quadratic form trivial. -/
theorem psd_trace_product_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosDef)
    (hzero : (A * B).trace = 0) : A = 0 := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [star_eq_conjTranspose, trace_mul_cycle, trace_mul_cycle] at hzero
  have hmat : C * B * Cᴴ = 0 :=
    (hB.posSemidef.mul_mul_conjTranspose_same C).trace_eq_zero_iff.mp hzero
  rw [Matrix.mul_assoc] at hmat
  have hC : C = 0 := by
    ext i j
    have hdiag : C i ⬝ᵥ (B *ᵥ C i) = 0 := by
      have h := congrArg (fun M : Matrix ι ι ℝ => M i i) hmat
      simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
        Matrix.zero_apply, dotProduct, mulVec] using h
    have hrow : C i = 0 := by
      by_contra hne
      have hp := hB.dotProduct_mulVec_pos hne
      simp only [star_trivial, hdiag, lt_self_iff_false] at hp
    exact congrFun hrow j
  simp [hC]

end WorstCaseVaR.KnownMoments
end


/- Inlined checked module: BorderedBasics -/
section
set_option autoImplicit false

open Matrix

namespace WorstCaseVaR.KnownMoments

def augment {n : ℕ} (x : Fin n → ℝ) (a : ℝ) : Fin n ⊕ Fin 1 → ℝ := Sum.elim x (fun _ => a)

theorem augment_decompose {n : ℕ} (u : Fin n ⊕ Fin 1 → ℝ) :
    u = augment (fun i => u (.inl i)) (u (.inr 0)) := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl

theorem bordered_hermitian {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (b : Fin n → ℝ) (c : ℝ) : (bordered A b c).IsHermitian :=
  hA.fromBlocks rfl rfl

theorem bordered_quadratic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b x : Fin n → ℝ) (c a : ℝ) :
    augment x a ⬝ᵥ (bordered A b c *ᵥ augment x a) =
      x ⬝ᵥ (A *ᵥ x) + 2 * a * (b ⬝ᵥ x) + c * a ^ 2 := by
  simp [augment, bordered, dotProduct, mulVec, Finset.sum_add_distrib,
    Finset.mul_sum, mul_add, mul_comm, mul_left_comm, mul_assoc]
  ring_nf
  rw [Finset.sum_mul]

theorem bordered_posSemidef_iff {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (b : Fin n → ℝ) (c : ℝ) :
    (bordered A b c).PosSemidef ↔
      ∀ x : Fin n → ℝ, ∀ a : ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x) + 2 * a * (b ⬝ᵥ x) + c * a ^ 2 := by
  constructor
  · intro h x a
    simpa only [star_trivial, bordered_quadratic] using h.dotProduct_mulVec_nonneg (augment x a)
  · intro h
    apply PosSemidef.of_dotProduct_mulVec_nonneg (bordered_hermitian hA b c)
    intro u
    rw [augment_decompose u]
    simpa only [star_trivial, bordered_quadratic] using h (fun i => u (.inl i)) (u (.inr 0))

theorem bordered_trace_product {n : ℕ} (A D : Matrix (Fin n) (Fin n) ℝ)
    (b e : Fin n → ℝ) (c f : ℝ) :
    (bordered A b c * bordered D e f).trace = (A * D).trace + 2 * (b ⬝ᵥ e) + c * f := by
  simp [bordered, Matrix.trace, Matrix.diag, Matrix.mul_apply, dotProduct,
    Finset.sum_add_distrib, Finset.mul_sum, mul_comm]
  ring_nf
  rw [Finset.sum_mul]
  ring

theorem bordered_zero_corner_forces_vector_zero {n : ℕ} (b : Fin n → ℝ) (c : ℝ)
    (h : (bordered 0 b c).PosSemidef) : b = 0 := by
  have hq := (bordered_posSemidef_iff (by simp) b c).mp h
  by_contra hb
  have hbb : 0 < b ⬝ᵥ b := by
    simpa only [star_trivial] using (dotProduct_star_self_pos_iff (v := b)).mpr hb
  let a := -(c + 1) / (2 * (b ⬝ᵥ b))
  have hz := hq (a • b) 1
  simp only [zero_mulVec, dotProduct_zero, dotProduct_smul, smul_eq_mul, one_pow, mul_one] at hz
  have heq : 2 * 1 * (a * (b ⬝ᵥ b)) + c = -1 := by
    dsimp [a]
    field_simp
    ring
  linarith

end WorstCaseVaR.KnownMoments
end


/- Inlined checked module: SecondMomentMatrix -/
section
set_option autoImplicit false

open Matrix

namespace WorstCaseVaR.KnownMoments

theorem secondMoment_quadratic {n : ℕ} (μ : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (a : ℝ) :
    augment x a ⬝ᵥ (secondMomentMatrix μ S *ᵥ augment x a) =
      x ⬝ᵥ (S *ᵥ x) + (⇑μ ⬝ᵥ x + a) ^ 2 := by
  rw [secondMomentMatrix, bordered_quadratic]
  simp only [momentS, add_mulVec, dotProduct_add, outer_quadratic, one_mul]
  rw [dotProduct_comm x ⇑μ]
  ring

theorem secondMoment_posDef {n : ℕ} (μ : EuclideanSpace ℝ (Fin n))
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) : (secondMomentMatrix μ S).PosDef := by
  have hμ : (vecMulVec ⇑μ ⇑μ).PosSemidef := by
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star ⇑μ
  apply PosDef.of_dotProduct_mulVec_pos
    (bordered_hermitian (hS.isHermitian.add hμ.isHermitian) ⇑μ 1)
  intro z hz
  let x := fun i => z (Sum.inl i)
  let a := z (Sum.inr 0)
  have heq : z = augment x a := augment_decompose z
  change 0 < z ⬝ᵥ (secondMomentMatrix μ S *ᵥ z)
  rw [heq, secondMoment_quadratic]
  by_cases hx : x = 0
  · have ha : a ≠ 0 := by
      intro ha
      apply hz
      rw [heq, hx, ha]
      funext i
      exact Sum.casesOn i (fun _ => rfl) (fun _ => rfl)
    simpa [hx] using sq_pos_of_ne_zero ha
  · have hp := hS.dotProduct_mulVec_pos hx
    simp only [star_trivial] at hp
    have hnonneg := sq_nonneg (⇑μ ⬝ᵥ x + a)
    linarith

end WorstCaseVaR.KnownMoments
end


/- Inlined checked module: QuadraticMoments -/
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix

namespace WorstCaseVaR.KnownMoments

theorem HasMeanCov.memLp_lift {n : ℕ} {P : Measure (EuclideanSpace ℝ (Fin n))}
    {μ : EuclideanSpace ℝ (Fin n)} {S : Matrix (Fin n) (Fin n) ℝ}
    (h : HasMeanCov P μ S) (i : Fin n ⊕ Fin 1) :
    MemLp (fun x : EuclideanSpace ℝ (Fin n) => liftVec ⇑x i) 2 P := by
  have : IsProbabilityMeasure P := h.isProbabilityMeasure
  cases i with
  | inl i => exact h.memLp_two i
  | inr i => exact memLp_const 1

theorem HasMeanCov.lift_raw_second {n : ℕ} {P : Measure (EuclideanSpace ℝ (Fin n))}
    {μ : EuclideanSpace ℝ (Fin n)} {S : Matrix (Fin n) (Fin n) ℝ}
    (h : HasMeanCov P μ S) (i j : Fin n ⊕ Fin 1) :
    (∫ x : EuclideanSpace ℝ (Fin n), liftVec ⇑x i * liftVec ⇑x j ∂P) = secondMomentMatrix μ S i j := by
  have : IsProbabilityMeasure P := h.isProbabilityMeasure
  cases i with
  | inl i =>
    cases j with
    | inl j => exact h.raw_second i j
    | inr j =>
      change (∫ x : EuclideanSpace ℝ (Fin n), x i * 1 ∂P) = μ i
      simpa using h.mean_eq i
  | inr i =>
    cases j with
    | inl j =>
      change (∫ x : EuclideanSpace ℝ (Fin n), 1 * x j ∂P) = μ j
      simpa using h.mean_eq j
    | inr j =>
      change (∫ _ : EuclideanSpace ℝ (Fin n), (1 : ℝ) * 1 ∂P) = 1
      simp

theorem HasMeanCov.quadFn_integrable {n : ℕ} {P : Measure (EuclideanSpace ℝ (Fin n))}
    {μ : EuclideanSpace ℝ (Fin n)} {S : Matrix (Fin n) (Fin n) ℝ}
    (h : HasMeanCov P μ S) (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => quadFn M ⇑x) P := by
  have : IsProbabilityMeasure P := h.isProbabilityMeasure
  change Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
    ∑ i : Fin n ⊕ Fin 1, liftVec ⇑x i * (∑ j, M i j * liftVec ⇑x j)) P
  simp_rw [Finset.mul_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact (h.memLp_lift i).integrable_mul ((h.memLp_lift j).const_mul (M i j))

/-- Quadratic integration is exactly the trace pairing with the supplied second-moment matrix. -/
theorem HasMeanCov.integral_quadFn {n : ℕ} {P : Measure (EuclideanSpace ℝ (Fin n))}
    {μ : EuclideanSpace ℝ (Fin n)} {S : Matrix (Fin n) (Fin n) ℝ}
    (h : HasMeanCov P μ S) (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin n), quadFn M ⇑x ∂P) = (M * secondMomentMatrix μ S).trace := by
  have : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hint (i j : Fin n ⊕ Fin 1) :
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => liftVec ⇑x i * (M i j * liftVec ⇑x j)) P :=
    (h.memLp_lift i).integrable_mul ((h.memLp_lift j).const_mul (M i j))
  change (∫ x : EuclideanSpace ℝ (Fin n),
    ∑ i : Fin n ⊕ Fin 1, liftVec ⇑x i * (∑ j, M i j * liftVec ⇑x j) ∂P) =
      ∑ i : Fin n ⊕ Fin 1, ∑ j, M i j * secondMomentMatrix μ S j i
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      have heq : (fun x : EuclideanSpace ℝ (Fin n) => liftVec ⇑x i * (M i j * liftVec ⇑x j)) =
          fun x : EuclideanSpace ℝ (Fin n) => M i j * (liftVec ⇑x j * liftVec ⇑x i) := by
        funext x
        ring
      rw [heq, integral_const_mul, h.lift_raw_second]
    · exact fun j _ => hint i j
  · exact fun i _ => integrable_finsetSum _ (fun j _ => hint i j)

end WorstCaseVaR.KnownMoments
end


/- Inlined checked module: SDPProbability -/
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

theorem certificate_quadratic {n : ℕ}
    (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (w x : Fin n → ℝ) (τ γ : ℝ) :
    quadFn (M + bordered 0 w (-τ + 2 * γ)) x = quadFn M x + 2 * (w ⬝ᵥ x) - τ + 2 * γ := by
  unfold quadFn
  rw [add_mulVec, dotProduct_add]
  change liftVec x ⬝ᵥ (M *ᵥ liftVec x) +
      augment x 1 ⬝ᵥ (bordered 0 w (-τ + 2 * γ) *ᵥ augment x 1) = _
  rw [bordered_quadratic]
  simp only [zero_mulVec, dotProduct_zero, one_pow, mul_one]
  ring

theorem sdp_implies_probability {n : ℕ} (μ w : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) (hw : w ≠ 0)
    (ε : ℝ) (hε : 0 ≤ ε) (γ : ℝ)
    (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (τ : ℝ)
    (htrace : (M * secondMomentMatrix μ S).trace ≤ τ * ε)
    (hM : M.PosSemidef) (hτ : 0 ≤ τ)
    (hcert : (M + bordered 0 ⇑w (-τ + 2 * γ)).PosSemidef) :
    ∀ P : Measure (EuclideanSpace ℝ (Fin n)), HasMeanCov P μ S →
      P (lossSet w γ) ≤ ENNReal.ofReal ε := by
  have hMoment := secondMoment_posDef μ hS
  have hτpos : 0 < τ := by
    by_contra hn
    have hz : τ = 0 := le_antisymm (le_of_not_gt hn) hτ
    have hnonneg := psd_trace_product_nonneg hM hMoment.posSemidef
    have htrzero : (M * secondMomentMatrix μ S).trace = 0 := by rw [hz] at htrace; linarith
    have hMz := psd_trace_product_eq_zero hM hMoment htrzero
    have hwz : (⇑w : Fin n → ℝ) = 0 := bordered_zero_corner_forces_vector_zero ⇑w (2 * γ)
      (by simpa only [hMz, hz, neg_zero, zero_add] using hcert)
    exact coe_ne_zero hw hwz
  intro P hP
  have : IsProbabilityMeasure P := hP.isProbabilityMeasure
  have hsub : lossSet w γ ⊆ {x | τ ≤ quadFn M ⇑x} := by
    intro x hx
    change γ ≤ -⟪w, x⟫_ℝ at hx
    have h := hcert.dotProduct_mulVec_nonneg (liftVec ⇑x)
    change 0 ≤ quadFn (M + bordered 0 ⇑w (-τ + 2 * γ)) ⇑x at h
    rw [certificate_quadratic] at h
    have hlin : (⇑w ⬝ᵥ ⇑x) = ⟪w, x⟫_ℝ := linearForm_eq_inner w x
    rw [hlin] at h
    change τ ≤ quadFn M ⇑x
    linarith
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := P) (f := fun x => quadFn M ⇑x)
    (ae_of_all _ (fun x => hM.dotProduct_mulVec_nonneg (liftVec ⇑x)))
    (hP.quadFn_integrable M) τ
  rw [hP.integral_quadFn] at hmarkov
  have hreal : P.real (lossSet w γ) ≤ ε := by
    apply (mul_le_mul_iff_right₀ hτpos).mp
    calc
      τ * P.real (lossSet w γ) ≤ τ * P.real {x | τ ≤ quadFn M ⇑x} :=
        mul_le_mul_of_nonneg_left (measureReal_mono hsub) hτ
      _ ≤ (M * secondMomentMatrix μ S).trace := hmarkov
      _ ≤ τ * ε := htrace
  apply (ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hε]
  exact hreal

end WorstCaseVaR.KnownMoments
end


/- Inlined checked module: RankOneCertificates -/
section
set_option autoImplicit false

open Matrix

namespace WorstCaseVaR.KnownMoments

noncomputable def rankOneShift {n : ℕ} (w : Fin n → ℝ) (a α : ℝ) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  α • vecMulVec (augment (-w) (-a)) (augment (-w) (-a))

theorem rankOneShift_posSemidef {n : ℕ} (w : Fin n → ℝ) (a α : ℝ) (hα : 0 ≤ α) :
    (rankOneShift w a α).PosSemidef := by
  have h : (vecMulVec (augment (-w) (-a)) (augment (-w) (-a))).PosSemidef := by
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star (augment (-w) (-a))
  exact h.smul hα

theorem scaled_outer_trace {ι : Type*} [Fintype ι] (α : ℝ)
    (z : ι → ℝ) (S : Matrix ι ι ℝ) :
    ((α • vecMulVec z z) * S).trace = α * (z ⬝ᵥ (S *ᵥ z)) := by
  rw [Matrix.smul_mul, trace_smul, smul_eq_mul, trace_mul_comm, mul_vecMulVec, trace_vecMulVec,
    dotProduct_comm]

theorem rankOneShift_trace {n : ℕ} (μ : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) (a α : ℝ) :
    (rankOneShift w a α * secondMomentMatrix μ S).trace =
      α * (portfolioVariance S w + (-linearForm w μ - a) ^ 2) := by
  rw [rankOneShift, scaled_outer_trace, secondMoment_quadratic]
  simp only [mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  rw [dotProduct_comm ⇑μ w]
  rfl

/-- Completing the square gives the exact matrix inequality in formulation 3. -/
theorem rankOneShift_certificate {n : ℕ} (w : Fin n → ℝ) (a τ : ℝ) (hτ : τ ≠ 0) :
    rankOneShift w a (1 / τ) + bordered 0 w (-τ + 2 * (a + τ)) =
      rankOneShift w (a + τ) (1 / τ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp [rankOneShift, bordered, augment, vecMulVec]
  all_goals field_simp
  all_goals ring

end WorstCaseVaR.KnownMoments
end


/- Inlined checked module: ScalarSDPCertificate -/
section
set_option autoImplicit false

open Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

theorem scalar_implies_sdp {n : ℕ} (μ w : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) (hw : w ≠ 0)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (γ : ℝ)
    (hscalar : kappa ε * Real.sqrt (⇑w ⬝ᵥ S *ᵥ ⇑w) - ⟪μ, w⟫_ℝ ≤ γ) :
    ∃ (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (τ : ℝ),
      (M * secondMomentMatrix μ S).trace ≤ τ * ε ∧ M.PosSemidef ∧ 0 ≤ τ ∧
      (M + bordered 0 ⇑w (-τ + 2 * γ)).PosSemidef := by
  let v := portfolioVariance S ⇑w
  let m := -linearForm ⇑w μ
  let δ := γ - m
  let a := m - v / δ
  let τ := δ + v / δ
  have hv : 0 < v := portfolioVariance_pos hS (coe_ne_zero hw)
  have hm : linearForm ⇑w μ = ⟪μ, w⟫_ℝ := by rw [linearForm_eq_inner, real_inner_comm]
  have hδbound : kappa ε * Real.sqrt v ≤ δ := by
    dsimp [δ, m, v, portfolioVariance]
    rw [hm]
    linarith
  have hδ : 0 < δ := (mul_pos (kappa_pos hε0 hε1) (Real.sqrt_pos.mpr hv)).trans_le hδbound
  have hτ : 0 < τ := add_pos hδ (div_pos hv hδ)
  have hden : 0 < v + δ ^ 2 := by positivity
  have hrel : a + τ = γ := by dsimp [a, τ, δ]; ring
  refine ⟨rankOneShift ⇑w a (1 / τ), τ, ?_, rankOneShift_posSemidef _ _ _ (by positivity), hτ.le, ?_⟩
  · rw [rankOneShift_trace]
    change (1 / τ) * (v + (m - a) ^ 2) ≤ τ * ε
    have heq : (1 / τ) * (v + (m - a) ^ 2) = v / δ := by
      dsimp [a, τ]
      field_simp
      ring
    rw [heq]
    apply (div_le_iff₀ hδ).2
    have hr := (tail_ratio_le_iff hv hδ.le hε0 hε1).mpr hδbound
    have hb := (div_le_iff₀ hden).mp hr
    have heq' : τ * ε * δ = ε * (v + δ ^ 2) := by
      dsimp [τ]
      field_simp
      ring
    rw [heq']
    exact hb
  · rw [← hrel, rankOneShift_certificate _ _ _ hτ.ne']
    exact rankOneShift_posSemidef _ _ _ (by positivity)

end WorstCaseVaR.KnownMoments
end


/- Inlined checked module: EllipsoidWitness -/
section
set_option autoImplicit false

open Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

theorem supported_border_posSemidef {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.PosSemidef) (y : Fin n → ℝ) :
    (bordered S (S *ᵥ y) (y ⬝ᵥ (S *ᵥ y))).PosSemidef := by
  apply (bordered_posSemidef_iff hS.isHermitian _ _).mpr
  intro x a
  have h := hS.dotProduct_mulVec_nonneg (x + a • y)
  simp only [star_trivial, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, symmetric_pairing hS.isHermitian y x] at h
  rw [dotProduct_comm (S *ᵥ y) x]
  nlinarith only [h]

theorem ellipsoid_witness {n : ℕ} (μ : EuclideanSpace ℝ (Fin n))
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) {w : Fin n → ℝ} (hw : w ≠ 0) (k : ℝ) :
    ∃ x : EuclideanSpace ℝ (Fin n), (bordered S ⇑(x - μ) (k ^ 2)).PosSemidef ∧
      -linearForm w x = k * Real.sqrt (portfolioVariance S w) - linearForm w μ := by
  let v := portfolioVariance S w
  let s := Real.sqrt v
  let y := (-(k / s)) • w
  let x := μ - (k / s) • WithLp.toLp 2 (S *ᵥ w)
  have hv : 0 < v := portfolioVariance_pos hS hw
  have hs : 0 < s := Real.sqrt_pos.mpr hv
  have hs2 : s ^ 2 = v := Real.sq_sqrt hv.le
  have hb : S *ᵥ y = ⇑(x - μ) := by
    ext i
    simp only [y, x, mulVec_smul, Pi.smul_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hc : y ⬝ᵥ (S *ᵥ y) = k ^ 2 := by
    simp only [y, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    change -(k / s) * (-(k / s) * v) = k ^ 2
    rw [← hs2]
    field_simp
  have hB := supported_border_posSemidef hS.posSemidef y
  rw [hc, hb] at hB
  refine ⟨x, hB, ?_⟩
  have hx : linearForm w x = linearForm w μ - k * s := by
    change w ⬝ᵥ (⇑μ - (k / s) • (S *ᵥ w)) = w ⬝ᵥ ⇑μ - k * s
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    change w ⬝ᵥ ⇑μ - (k / s) * v = w ⬝ᵥ ⇑μ - k * s
    rw [← hs2]
    field_simp
  rw [hx]
  change -(linearForm w μ - k * s) = k * s - linearForm w μ
  ring

theorem ellipsoid_implies_scalar {n : ℕ} (μ w : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) (hw : w ≠ 0) (ε γ : ℝ)
    (hrobust : ∀ x : EuclideanSpace ℝ (Fin n),
      (bordered S ⇑(x - μ) (kappa ε ^ 2)).PosSemidef → -⟪x, w⟫_ℝ ≤ γ) :
    kappa ε * Real.sqrt (⇑w ⬝ᵥ S *ᵥ ⇑w) - ⟪μ, w⟫_ℝ ≤ γ := by
  obtain ⟨x, hx, hvalue⟩ := ellipsoid_witness μ hS (coe_ne_zero hw) (kappa ε)
  have h := hrobust x hx
  rw [linearForm_eq_inner w x, linearForm_eq_inner w μ, real_inner_comm x w,
    real_inner_comm μ w] at hvalue
  change kappa ε * Real.sqrt (portfolioVariance S ⇑w) - ⟪μ, w⟫_ℝ ≤ γ
  rw [← hvalue]
  exact h

end WorstCaseVaR.KnownMoments
end


/- Inlined checked module: DualEllipsoid -/
section
set_option autoImplicit false

open Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

theorem scalar_implies_dual {n : ℕ} (μ w : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) (hw : w ≠ 0)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (γ : ℝ)
    (hscalar : kappa ε * Real.sqrt (⇑w ⬝ᵥ S *ᵥ ⇑w) - ⟪μ, w⟫_ℝ ≤ γ) :
    ∃ (L : Matrix (Fin n) (Fin n) ℝ) (c : ℝ), L.IsSymm ∧
      (L * S).trace + kappa ε ^ 2 * c - ⟪μ, w⟫_ℝ ≤ γ ∧
      (bordered L ((1 / 2 : ℝ) • ⇑w) c).PosSemidef := by
  let v := portfolioVariance S ⇑w
  let s := Real.sqrt v
  let k := kappa ε
  let L : Matrix (Fin n) (Fin n) ℝ := (k / (2 * s)) • vecMulVec ⇑w ⇑w
  let c := s / (2 * k)
  have hv : 0 < v := portfolioVariance_pos hS (coe_ne_zero hw)
  have hs : 0 < s := Real.sqrt_pos.mpr hv
  have hk : 0 < k := kappa_pos hε0 hε1
  have hs2 : s ^ 2 = v := Real.sq_sqrt hv.le
  have hO : (vecMulVec ⇑w ⇑w).PosSemidef := by
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star ⇑w
  have hL : L.PosSemidef := hO.smul (by positivity)
  refine ⟨L, c, isHermitian_iff_isSymm.mp hL.isHermitian, ?_, ?_⟩
  · change (((k / (2 * s)) • vecMulVec ⇑w ⇑w) * S).trace + k ^ 2 * c - ⟪μ, w⟫_ℝ ≤ γ
    rw [scaled_outer_trace]
    change (k / (2 * s)) * v + k ^ 2 * (s / (2 * k)) - ⟪μ, w⟫_ℝ ≤ γ
    have heq : (k / (2 * s)) * v + k ^ 2 * (s / (2 * k)) = k * s := by
      rw [← hs2]
      field_simp
      ring
    rw [heq]
    exact hscalar
  · have hZ : (vecMulVec (augment ((k / s) • ⇑w) 1) (augment ((k / s) • ⇑w) 1)).PosSemidef := by
      simpa only [star_trivial] using posSemidef_vecMulVec_self_star (augment ((k / s) • ⇑w) 1)
    have heq : bordered L ((1 / 2 : ℝ) • ⇑w) c =
        c • vecMulVec (augment ((k / s) • ⇑w) 1) (augment ((k / s) • ⇑w) 1) := by
      ext i j
      rcases i with i | i <;> rcases j with j | j
      all_goals simp [bordered, L, c, augment, vecMulVec]
      all_goals field_simp
    rw [heq]
    exact hZ.smul (by dsimp [c]; positivity)

theorem dual_implies_ellipsoid {n : ℕ} (μ w : EuclideanSpace ℝ (Fin n))
    (S L : Matrix (Fin n) (Fin n) ℝ) (ε γ c : ℝ)
    (hobj : (L * S).trace + kappa ε ^ 2 * c - ⟪μ, w⟫_ℝ ≤ γ)
    (hcert : (bordered L ((1 / 2 : ℝ) • ⇑w) c).PosSemidef) :
    ∀ x : EuclideanSpace ℝ (Fin n),
      (bordered S ⇑(x - μ) (kappa ε ^ 2)).PosSemidef → -⟪x, w⟫_ℝ ≤ γ := by
  intro x hx
  have htr := psd_trace_product_nonneg hcert hx
  rw [bordered_trace_product] at htr
  change 0 ≤ (L * S).trace + 2 * (((1 / 2 : ℝ) • ⇑w) ⬝ᵥ (⇑x - ⇑μ)) + c * kappa ε ^ 2 at htr
  rw [smul_dotProduct, smul_eq_mul, dotProduct_sub] at htr
  have hi : (⇑w ⬝ᵥ ⇑x) = ⟪x, w⟫_ℝ := by rw [← real_inner_comm]; exact linearForm_eq_inner w x
  have hm : (⇑w ⬝ᵥ ⇑μ) = ⟪μ, w⟫_ℝ := by rw [← real_inner_comm]; exact linearForm_eq_inner w μ
  rw [hi, hm] at htr
  nlinarith

end WorstCaseVaR.KnownMoments
end


/- Inlined checked module: VaRRoot -/
section
set_option autoImplicit false

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

/-- **Theorem 1** (El Ghaoui–Oks–Oustry 2003, pp. 545–546). Let `𝒫` be the set of probability
distributions on `ℝⁿ` with mean `x̂` and covariance matrix `Γ ≻ 0`, let `w ≠ 0`,
`ε ∈ (0, 1)` and `γ ∈ ℝ`. The following are equivalent:
1. `sup_{P ∈ 𝒫} Prob{γ ≤ -wᵀx} ≤ ε`;
2. `κ(ε) ‖Γ^{1/2} w‖₂ - x̂ᵀw ≤ γ` (7);
3. there exist `M ∈ 𝒮_{n+1}`, `τ ∈ ℝ` with `⟨M, Σ⟩ ≤ τε`, `M ⪰ 0`, `τ ≥ 0`,
   `M + [[0, w], [wᵀ, -τ + 2γ]] ⪰ 0` (9);
4. for every `x` with `[[Γ, x - x̂], [(x - x̂)ᵀ, κ(ε)²]] ⪰ 0` (10), `-xᵀw ≤ γ`;
5. there exist `Λ ∈ 𝒮_n`, `v ∈ ℝ` with `⟨Λ, Γ⟩ + κ(ε)² v - x̂ᵀw ≤ γ` and
   `[[Λ, w/2], [wᵀ/2, v]] ⪰ 0` (11).
The printed range `ε ∈ (0, 1]` is read as `(0, 1)`: at `ε = 1` item 1 holds for every `γ`. -/
theorem worst_case_var_equivalences {n : ℕ}
    (xhat w : EuclideanSpace ℝ (Fin n)) (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.PosDef)
    (hw : w ≠ 0) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (γ : ℝ) :
    List.TFAE
      [ ∀ P : Measure (EuclideanSpace ℝ (Fin n)), HasMeanCov P xhat Γ →
          P (lossSet w γ) ≤ ENNReal.ofReal ε,
        kappa ε * Real.sqrt (⇑w ⬝ᵥ Γ *ᵥ ⇑w) - ⟪xhat, w⟫_ℝ ≤ γ,
        ∃ (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (τ : ℝ),
          (M * secondMomentMatrix xhat Γ).trace ≤ τ * ε ∧ M.PosSemidef ∧ 0 ≤ τ ∧
          (M + bordered 0 ⇑w (-τ + 2 * γ)).PosSemidef,
        ∀ x : EuclideanSpace ℝ (Fin n),
          (bordered Γ ⇑(x - xhat) (kappa ε ^ 2)).PosSemidef → -⟪x, w⟫_ℝ ≤ γ,
        ∃ (Λ : Matrix (Fin n) (Fin n) ℝ) (v : ℝ), Λ.IsSymm ∧
          (Λ * Γ).trace + kappa ε ^ 2 * v - ⟪xhat, w⟫_ℝ ≤ γ ∧
          (bordered Λ ((1 / 2 : ℝ) • ⇑w) v).PosSemidef ] := by
  tfae_have 1 ↔ 2 := probability_iff_scalar xhat w Γ hΓ hw ε hε0 hε1 γ
  tfae_have 2 → 3 := scalar_implies_sdp xhat w Γ hΓ hw ε hε0 hε1 γ
  tfae_have 3 → 1 := by
    rintro ⟨M, τ, htrace, hM, hτ, hcert⟩
    exact sdp_implies_probability xhat w Γ hΓ hw ε hε0.le γ M τ htrace hM hτ hcert
  tfae_have 2 → 5 := scalar_implies_dual xhat w Γ hΓ hw ε hε0 hε1 γ
  tfae_have 5 → 4 := by
    rintro ⟨L, c, _hL, hobj, hcert⟩
    exact dual_implies_ellipsoid xhat w Γ L ε γ c hobj hcert
  tfae_have 4 → 2 := ellipsoid_implies_scalar xhat w Γ hΓ hw ε γ
  tfae_finish

end WorstCaseVaR.KnownMoments
end


open MeasureTheory Matrix WorstCaseVaR.KnownMoments
open scoped InnerProductSpace

theorem solution {n : ℕ}
    (xhat w : EuclideanSpace ℝ (Fin n)) (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.PosDef)
    (hw : w ≠ 0) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (γ : ℝ) :
    List.TFAE
      [ ∀ P : Measure (EuclideanSpace ℝ (Fin n)), HasMeanCov P xhat Γ →
          P (lossSet w γ) ≤ ENNReal.ofReal ε,
        kappa ε * Real.sqrt (⇑w ⬝ᵥ Γ *ᵥ ⇑w) - ⟪xhat, w⟫_ℝ ≤ γ,
        ∃ (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (τ : ℝ),
          (M * secondMomentMatrix xhat Γ).trace ≤ τ * ε ∧ M.PosSemidef ∧ 0 ≤ τ ∧
          (M + bordered 0 ⇑w (-τ + 2 * γ)).PosSemidef,
        ∀ x : EuclideanSpace ℝ (Fin n),
          (bordered Γ ⇑(x - xhat) (kappa ε ^ 2)).PosSemidef → -⟪x, w⟫_ℝ ≤ γ,
        ∃ (Λ : Matrix (Fin n) (Fin n) ℝ) (v : ℝ), Λ.IsSymm ∧
          (Λ * Γ).trace + kappa ε ^ 2 * v - ⟪xhat, w⟫_ℝ ≤ γ ∧
          (bordered Λ ((1 / 2 : ℝ) • ⇑w) v).PosSemidef ] := WorstCaseVaR.KnownMoments.worst_case_var_equivalences xhat w Γ hΓ hw ε hε0 hε1 γ
