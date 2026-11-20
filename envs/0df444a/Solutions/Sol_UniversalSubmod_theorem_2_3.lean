-- Prove2me | solution 1 for UniversalSubmod.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:10:07.237756+00:00
-- url     : https://prove2.me/submissions/7e614a34-95a7-40c9-97c4-8758b3e06827

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_Cohen2019_Robust_Phi
import Definitions.Def_UniversalSubmod_CorrMatrix
import Definitions.Def_UniversalSubmod_semidefExt
import Theorems.Thm_UniversalSubmod_claim_A_1
import Theorems.Thm_UniversalSubmod_eq_2_second_partials

section
set_option autoImplicit false

namespace UniversalSubmod.Dev.Thm23

open MeasureTheory ProbabilityTheory Cohen2019.Robust

variable {n : ℕ}

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- the interpolation `cos θ X + sin θ Y` as a continuous linear map -/
noncomputable def Lz (n : ℕ) (θ : ℝ) : (E n × E n) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    Real.cos θ • ((EuclideanSpace.proj i : E n →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ (E n) (E n)))
    + Real.sin θ • ((EuclideanSpace.proj i : E n →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ (E n) (E n)))

lemma Lz_apply (θ : ℝ) (ω : E n × E n) (i : Fin n) :
    Lz n θ ω i = Real.cos θ * ω.1 i + Real.sin θ * ω.2 i := by
  simp [Lz]

section prodspace
variable {S S' : Matrix (Fin n) (Fin n) ℝ}

lemma hgl1 (i : Fin n) : HasGaussianLaw (fun ω : E n × E n => ω.1 i)
    ((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) :=
  (IsGaussian.hasGaussianLaw_id (μ := (multivariateGaussian 0 S).prod (multivariateGaussian 0 S'))).map_fun
    ((EuclideanSpace.proj i : E n →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ (E n) (E n)))

lemma hgl2 (i : Fin n) : HasGaussianLaw (fun ω : E n × E n => ω.2 i)
    ((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) :=
  (IsGaussian.hasGaussianLaw_id (μ := (multivariateGaussian 0 S).prod (multivariateGaussian 0 S'))).map_fun
    ((EuclideanSpace.proj i : E n →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ (E n) (E n)))

lemma int_eval (S : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    ∫ x, x i ∂(multivariateGaussian 0 S) = 0 := by
  have := (EuclideanSpace.proj i : E n →L[ℝ] ℝ).integral_comp_id_comm
    (μ := multivariateGaussian 0 S) IsGaussian.integrable_id
  simpa [integral_id_multivariateGaussian] using this

lemma int1 (i : Fin n) : ∫ ω : E n × E n, ω.1 i
    ∂((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) = 0 := by
  rw [integral_fun_fst (fun x : E n => x i)]; simp [int_eval]

lemma int2 (i : Fin n) : ∫ ω : E n × E n, ω.2 i
    ∂((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) = 0 := by
  rw [integral_fun_snd (fun x : E n => x i)]; simp [int_eval]

lemma cov11 (hS : S.PosSemidef) (i j : Fin n) :
    cov[fun ω : E n × E n => ω.1 i, fun ω : E n × E n => ω.1 j;
      (multivariateGaussian 0 S).prod (multivariateGaussian 0 S')] = S i j := by
  have h := covariance_map (X := fun x : E n => x i) (Y := fun x : E n => x j)
    (μ := (multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) (Z := Prod.fst)
    (by fun_prop) (by fun_prop) (by fun_prop)
  rw [Measure.map_fst_prod] at h
  simp at h
  rw [← covariance_eval_multivariateGaussian (μ := 0) hS i j]
  exact h.symm

lemma cov22 (hS' : S'.PosSemidef) (i j : Fin n) :
    cov[fun ω : E n × E n => ω.2 i, fun ω : E n × E n => ω.2 j;
      (multivariateGaussian 0 S).prod (multivariateGaussian 0 S')] = S' i j := by
  have h := covariance_map (X := fun x : E n => x i) (Y := fun x : E n => x j)
    (μ := (multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) (Z := Prod.snd)
    (by fun_prop) (by fun_prop) (by fun_prop)
  rw [Measure.map_snd_prod] at h
  simp at h
  rw [← covariance_eval_multivariateGaussian (μ := 0) hS' i j]
  exact h.symm

lemma cov12 (i j : Fin n) :
    cov[fun ω : E n × E n => ω.1 i, fun ω : E n × E n => ω.2 j;
      (multivariateGaussian 0 S).prod (multivariateGaussian 0 S')] = 0 := by
  have := (covariance_fst_snd_prod (μ := multivariateGaussian 0 S) (ν := multivariateGaussian 0 S')
    (X := fun x : E n => x i) (Y := fun x : E n => x j) (by
      have := (IsGaussian.hasGaussianLaw_id (μ := multivariateGaussian 0 S)).map_fun
        (EuclideanSpace.proj i : E n →L[ℝ] ℝ)
      exact this.memLp_two) (by
      have := (IsGaussian.hasGaussianLaw_id (μ := multivariateGaussian 0 S')).map_fun
        (EuclideanSpace.proj j : E n →L[ℝ] ℝ)
      exact this.memLp_two))
  exact this


noncomputable def D (i : Fin n) (g : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) : ℝ :=
  fderiv ℝ g y (Pi.single i (1 : ℝ))

lemma fderiv_eq_sum (g : (Fin n → ℝ) → ℝ) (y a : Fin n → ℝ) :
    fderiv ℝ g y a = ∑ j, a j * D j g y := by
  have h : a = ∑ j, a j • (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h]
  simp [map_sum, D]

lemma Lz_cont (θ : ℝ) : Continuous (Lz n θ) := (Lz n θ).continuous

lemma int_Lz (θ : ℝ) (j : Fin n) :
    ∫ ω, Lz n θ ω j ∂((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) = 0 := by
  simp_rw [Lz_apply]
  rw [integral_add, integral_const_mul, integral_const_mul, int1, int2]
  · simp
  · exact ((hgl1 (S := S) (S' := S') j).integrable.const_mul _)
  · exact ((hgl2 (S := S) (S' := S') j).integrable.const_mul _)

lemma cov_fst_Lz (hS : S.PosSemidef) (θ : ℝ) (i j : Fin n) :
    cov[fun ω : E n × E n => ω.1 i, fun ω : E n × E n => Lz n θ ω j;
      (multivariateGaussian 0 S).prod (multivariateGaussian 0 S')] = Real.cos θ * S i j := by
  simp_rw [Lz_apply]
  have h1 := (hgl1 (S := S) (S' := S') i).memLp_two
  have h2 := (hgl1 (S := S) (S' := S') j).memLp_two
  have h3 := (hgl2 (S := S) (S' := S') j).memLp_two
  have := covariance_add_right h1 (h2.const_mul (Real.cos θ)) (h3.const_mul (Real.sin θ))
  simp only [Pi.add_def] at this
  rw [this, covariance_const_mul_right, covariance_const_mul_right, cov11 hS, cov12]
  ring

lemma cov_snd_Lz (hS' : S'.PosSemidef) (θ : ℝ) (i j : Fin n) :
    cov[fun ω : E n × E n => ω.2 i, fun ω : E n × E n => Lz n θ ω j;
      (multivariateGaussian 0 S).prod (multivariateGaussian 0 S')] = Real.sin θ * S' i j := by
  simp_rw [Lz_apply]
  have h1 := (hgl2 (S := S) (S' := S') i).memLp_two
  have h2 := (hgl1 (S := S) (S' := S') j).memLp_two
  have h3 := (hgl2 (S := S) (S' := S') j).memLp_two
  have := covariance_add_right h1 (h2.const_mul (Real.cos θ)) (h3.const_mul (Real.sin θ))
  simp only [Pi.add_def] at this
  rw [this, covariance_const_mul_right, covariance_const_mul_right, cov22 hS', covariance_comm, cov12]
  ring

lemma stein_Z (A : (E n × E n) →L[ℝ] ℝ) (hA0 : ∫ ω, A ω
      ∂((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) = 0)
    (θ : ℝ) (g : (Fin n → ℝ) → ℝ) (hg : ContDiff ℝ 1 g)
    (hgb : ∃ C : ℝ, ∀ x j, |D j g x| ≤ C) :
    ∫ ω, A ω * g (Lz n θ ω) ∂((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) =
      ∑ j, cov[fun ω => A ω, fun ω => Lz n θ ω j;
        (multivariateGaussian 0 S).prod (multivariateGaussian 0 S')] *
        ∫ ω, D j g (Lz n θ ω) ∂((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) := by
  have h := UniversalSubmod.claim_A_1
    ((multivariateGaussian 0 S).prod (multivariateGaussian 0 S'))
    (fun ω => A ω) (fun j ω => Lz n θ ω j)
    (by
      have := (IsGaussian.hasGaussianLaw_id (μ := (multivariateGaussian 0 S).prod (multivariateGaussian 0 S'))).map_fun
        (A.prod (Lz n θ))
      exact this)
    hA0 (fun j => int_Lz θ j) g hg hgb
  exact h

lemma D_contDiff (H : (Fin n → ℝ) → ℝ) (hH : ContDiff ℝ 2 H) (i : Fin n) :
    ContDiff ℝ 1 (D i H) := by
  have : ContDiff ℝ 1 (fderiv ℝ H) := hH.fderiv_right (by norm_num)
  exact this.clm_apply contDiff_const

lemma int_bdd_mul (a : (E n × E n) → ℝ) (ha : Integrable a ((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')))
    (b : (E n × E n) → ℝ) (hb : Continuous b) (C : ℝ) (hC : ∀ ω, |b ω| ≤ C) :
    Integrable (fun ω => b ω * a ω) ((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) := by
  refine Integrable.mono' (ha.norm.const_mul C) (hb.aestronglyMeasurable.mul ha.aestronglyMeasurable)
    (ae_of_all _ fun ω => ?_)
  simp only [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hC ω) (abs_nonneg _)

theorem deriv_formula (hS : S.PosSemidef) (hS' : S'.PosSemidef) (H : (Fin n → ℝ) → ℝ)
    (hH : ContDiff ℝ 2 H) (C1 : ℝ) (hC1 : ∀ y i, |D i H y| ≤ C1)
    (C2 : ℝ) (hC2 : ∀ y i j, |D j (D i H) y| ≤ C2) (θ : ℝ) :
    ∫ ω, (∑ i, D i H (Lz n θ ω) * (-Real.sin θ * ω.1 i + Real.cos θ * ω.2 i))
      ∂((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) =
    Real.sin θ * Real.cos θ * ∑ i, ∑ j, (S' i j - S i j) *
      ∫ ω, D j (D i H) (Lz n θ ω) ∂((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) := by
  have hDc : ∀ i, Continuous (D i H) := fun i => (D_contDiff H hH i).continuous
  have e1 : ∀ i, ∫ ω, D i H (Lz n θ ω) * ω.1 i
      ∂((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) =
      Real.cos θ * ∑ j, S i j * ∫ ω, D j (D i H) (Lz n θ ω)
        ∂((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) := by
    intro i
    have := stein_Z (S := S) (S' := S')
      ((EuclideanSpace.proj i : E n →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ (E n) (E n)))
      (int1 i) θ (D i H) (D_contDiff H hH i) ⟨C2, fun x j => hC2 x i j⟩
    have this' : ∫ ω : E n × E n, ω.1 i * D i H (Lz n θ ω)
        ∂((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) =
        ∑ j, cov[fun ω : E n × E n => ω.1 i, fun ω : E n × E n => Lz n θ ω j;
          (multivariateGaussian 0 S).prod (multivariateGaussian 0 S')] *
        ∫ ω, D j (D i H) (Lz n θ ω) ∂((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) := this
    simp_rw [mul_comm (D i H _)]
    rw [this', Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cov_fst_Lz hS]; ring
  have e2 : ∀ i, ∫ ω, D i H (Lz n θ ω) * ω.2 i
      ∂((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) =
      Real.sin θ * ∑ j, S' i j * ∫ ω, D j (D i H) (Lz n θ ω)
        ∂((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) := by
    intro i
    have := stein_Z (S := S) (S' := S')
      ((EuclideanSpace.proj i : E n →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ (E n) (E n)))
      (int2 i) θ (D i H) (D_contDiff H hH i) ⟨C2, fun x j => hC2 x i j⟩
    have this' : ∫ ω : E n × E n, ω.2 i * D i H (Lz n θ ω)
        ∂((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) =
        ∑ j, cov[fun ω : E n × E n => ω.2 i, fun ω : E n × E n => Lz n θ ω j;
          (multivariateGaussian 0 S).prod (multivariateGaussian 0 S')] *
        ∫ ω, D j (D i H) (Lz n θ ω) ∂((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) := this
    simp_rw [mul_comm (D i H _)]
    rw [this', Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cov_snd_Lz hS']; ring
  have hint1 : ∀ i, Integrable (fun ω : E n × E n => D i H (Lz n θ ω) * ω.1 i)
      ((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) := fun i =>
    int_bdd_mul _ (hgl1 i).integrable _ ((hDc i).comp (Lz_cont θ)) C1 fun ω => hC1 _ _
  have hint2 : ∀ i, Integrable (fun ω : E n × E n => D i H (Lz n θ ω) * ω.2 i)
      ((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) := fun i =>
    int_bdd_mul _ (hgl2 i).integrable _ ((hDc i).comp (Lz_cont θ)) C1 fun ω => hC1 _ _
  have : ∀ ω : E n × E n, (∑ i, D i H (Lz n θ ω) * (-Real.sin θ * ω.1 i + Real.cos θ * ω.2 i)) =
      ∑ i, (-Real.sin θ * (D i H (Lz n θ ω) * ω.1 i) + Real.cos θ * (D i H (Lz n θ ω) * ω.2 i)) := by
    intro ω; refine Finset.sum_congr rfl fun i _ => by ring
  simp_rw [this]
  have hI : ∀ i ∈ (Finset.univ : Finset (Fin n)), Integrable (fun ω : E n × E n =>
      (-Real.sin θ * (D i H (Lz n θ ω) * ω.1 i) + Real.cos θ * (D i H (Lz n θ ω) * ω.2 i)))
      ((multivariateGaussian 0 S).prod (multivariateGaussian 0 S')) :=
    fun i _ => ((hint1 i).const_mul _).add ((hint2 i).const_mul _)
  rw [integral_finsetSum _ hI]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_add ((hint1 i).const_mul _) ((hint2 i).const_mul _), integral_const_mul,
    integral_const_mul, e1, e2, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem comparison (hS : S.PosSemidef) (hS' : S'.PosSemidef)
    (hle : ∀ i j, i ≠ j → S i j ≤ S' i j) (hdiag : ∀ i, S i i = S' i i)
    (H : (Fin n → ℝ) → ℝ) (hH : ContDiff ℝ 2 H) (C0 : ℝ) (hC0 : ∀ y, |H y| ≤ C0)
    (C1 : ℝ) (hC1 : ∀ y i, |D i H y| ≤ C1)
    (C2 : ℝ) (hC2 : ∀ y i j, |D j (D i H) y| ≤ C2)
    (hneg : ∀ y i j, i ≠ j → D j (D i H) y ≤ 0) :
    ∫ g : E n, H (fun i => g i) ∂(multivariateGaussian 0 S') ≤
      ∫ g : E n, H (fun i => g i) ∂(multivariateGaussian 0 S) := by
  set P := (multivariateGaussian 0 S).prod (multivariateGaussian 0 S') with hP
  have hHc : Continuous H := hH.continuous
  have hHd : Differentiable ℝ H := hH.differentiable (by norm_num)
  set φ : ℝ → ℝ := fun θ => ∫ ω, H (Lz n θ ω) ∂P with hφ
  have hderiv : ∀ θ, HasDerivAt φ (∫ ω, (∑ i, D i H (Lz n θ ω) * (-Real.sin θ * ω.1 i + Real.cos θ * ω.2 i)) ∂P) θ := by
    intro θ₀
    have hmeasF : ∀ θ, AEStronglyMeasurable (fun ω : E n × E n => H (Lz n θ ω)) P := fun θ =>
      (hHc.comp (Lz_cont θ)).aestronglyMeasurable
    have hDc : ∀ i, Continuous (D i H) := fun i => (D_contDiff H hH i).continuous
    have hb : Integrable (fun ω : E n × E n => C1 * ∑ i, (|ω.1 i| + |ω.2 i|)) P := by
      refine Integrable.const_mul (integrable_finsetSum _ fun i _ => ?_) _
      exact (hgl1 (S := S) (S' := S') i).integrable.norm.add (hgl2 (S := S) (S' := S') i).integrable.norm
    have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P) (𝕜 := ℝ)
      (F := fun θ ω => H (Lz n θ ω))
      (F' := fun θ ω => ∑ i, D i H (Lz n θ ω) * (-Real.sin θ * ω.1 i + Real.cos θ * ω.2 i))
      (x₀ := θ₀) (s := Set.univ) Filter.univ_mem
      (Filter.Eventually.of_forall hmeasF)
      (by
        refine Integrable.mono' (integrable_const C0) (hmeasF θ₀) (ae_of_all _ fun ω => ?_)
        simpa using hC0 _)
      (by
        refine Continuous.aestronglyMeasurable ?_
        refine continuous_finsetSum _ fun i _ => ?_
        refine ((hDc i).comp (Lz_cont θ₀)).mul ?_
        have : Continuous (fun ω : E n × E n => ω.1 i) :=
          ((EuclideanSpace.proj i : E n →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ (E n) (E n))).continuous
        have : Continuous (fun ω : E n × E n => ω.2 i) :=
          ((EuclideanSpace.proj i : E n →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ (E n) (E n))).continuous
        fun_prop)
      (bound := fun ω => C1 * ∑ i, (|ω.1 i| + |ω.2 i|))
      (ae_of_all _ fun ω θ _ => by
        rw [Real.norm_eq_abs]
        calc |∑ i, D i H (Lz n θ ω) * (-Real.sin θ * ω.1 i + Real.cos θ * ω.2 i)|
            ≤ ∑ i, |D i H (Lz n θ ω) * (-Real.sin θ * ω.1 i + Real.cos θ * ω.2 i)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, C1 * (|ω.1 i| + |ω.2 i|) := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [abs_mul]
              refine mul_le_mul (hC1 _ _) ?_ (abs_nonneg _) ((abs_nonneg _).trans (hC1 0 i))
              calc |-Real.sin θ * ω.1 i + Real.cos θ * ω.2 i|
                  ≤ |-Real.sin θ * ω.1 i| + |Real.cos θ * ω.2 i| := abs_add_le _ _
                _ ≤ |ω.1 i| + |ω.2 i| := by
                    have e1 : |-Real.sin θ * ω.1 i| ≤ |ω.1 i| := by
                      rw [abs_mul, abs_neg]
                      exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)
                    have e2 : |Real.cos θ * ω.2 i| ≤ |ω.2 i| := by
                      rw [abs_mul]
                      exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)
                    linarith
          _ = C1 * ∑ i, (|ω.1 i| + |ω.2 i|) := by rw [Finset.mul_sum])
      hb
      (ae_of_all _ fun ω θ _ => by
        have h1 : HasDerivAt (fun θ : ℝ => (Lz n θ ω : Fin n → ℝ))
            (fun i => -Real.sin θ * ω.1 i + Real.cos θ * ω.2 i) θ := by
          refine hasDerivAt_pi.2 fun i => ?_
          simp_rw [Lz_apply]
          exact (((Real.hasDerivAt_cos θ).mul_const (ω.1 i)).fun_add
            ((Real.hasDerivAt_sin θ).mul_const (ω.2 i))).congr_deriv (by ring)
        have h2 := (hHd (Lz n θ ω)).hasFDerivAt.comp_hasDerivAt θ h1
        convert h2 using 1
        rw [Function.comp_def]
        rw [fderiv_eq_sum]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _)
    exact this.2
  have hφ' : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), deriv φ θ ≤ 0 := by
    intro θ hθ
    rw [(hderiv θ).deriv, deriv_formula hS hS' H hH C1 hC1 C2 hC2 θ]
    have hsc : 0 ≤ Real.sin θ * Real.cos θ :=
      mul_nonneg (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])).le
        (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩).le
    refine mul_nonpos_of_nonneg_of_nonpos hsc (Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_)
    by_cases hij : i = j
    · subst hij; simp [hdiag]
    · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (hle i j hij))
        (integral_nonpos fun ω => hneg _ i j hij)
  have hanti : AntitoneOn φ (Set.Icc 0 (Real.pi / 2)) :=
    antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun θ _ => (hderiv θ).continuousAt.continuousWithinAt)
      (fun θ _ => (hderiv θ).differentiableAt.differentiableWithinAt)
      (by rwa [interior_Icc])
  have h := hanti ⟨le_refl _, by linarith [Real.pi_pos]⟩ ⟨by linarith [Real.pi_pos], le_refl _⟩
    (by linarith [Real.pi_pos])
  have e0 : φ 0 = ∫ g : E n, H (fun i => g i) ∂(multivariateGaussian 0 S) := by
    simp only [hφ]
    have : ∀ ω : E n × E n, Lz n 0 ω = fun i => ω.1 i := by
      intro ω; ext i; simp [Lz_apply]
    simp_rw [this]
    rw [hP, integral_fun_fst (fun x : E n => H (fun i => x i))]
    simp
  have e1 : φ (Real.pi / 2) = ∫ g : E n, H (fun i => g i) ∂(multivariateGaussian 0 S') := by
    simp only [hφ]
    have : ∀ ω : E n × E n, Lz n (Real.pi / 2) ω = fun i => ω.2 i := by
      intro ω; ext i; simp [Lz_apply]
    simp_rw [this]
    rw [hP, integral_fun_snd (fun x : E n => H (fun i => x i))]
    simp
  rw [← e0, ← e1]; exact h

end prodspace
/-- bounded first and second derivatives, `C²` -/
def B2 (g : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 g ∧ (∃ C, ∀ t, |deriv g t| ≤ C) ∧ (∃ C, ∀ t, |deriv (deriv g) t| ≤ C)

lemma B2.comp {g s : ℝ → ℝ} (hg : B2 g) (hs : B2 s) : B2 (fun t => g (s t)) := by
  obtain ⟨hg2, ⟨Cg1, hg1⟩, ⟨Cg2, hg2'⟩⟩ := hg
  obtain ⟨hs2, ⟨Cs1, hs1⟩, ⟨Cs2, hs2'⟩⟩ := hs
  have hgd : Differentiable ℝ g := hg2.differentiable (by norm_num)
  have hsd : Differentiable ℝ s := hs2.differentiable (by norm_num)
  have hg'd : Differentiable ℝ (deriv g) :=
    ((contDiff_succ_iff_deriv (n := 1)).1 hg2).2.2.differentiable (by norm_num)
  have hs'd : Differentiable ℝ (deriv s) :=
    ((contDiff_succ_iff_deriv (n := 1)).1 hs2).2.2.differentiable (by norm_num)
  have hder : deriv (fun t => g (s t)) = fun t => deriv g (s t) * deriv s t := by
    funext t
    exact deriv_comp t (hgd _) (hsd t)
  refine ⟨hg2.comp hs2, ⟨Cg1 * Cs1, fun t => ?_⟩, ⟨Cg2 * Cs1 * Cs1 + Cg1 * Cs2, fun t => ?_⟩⟩
  · rw [hder]; simp only [abs_mul]
    exact mul_le_mul (hg1 _) (hs1 t) (abs_nonneg _) ((abs_nonneg _).trans (hg1 0))
  · rw [hder]
    have : deriv (fun t => deriv g (s t) * deriv s t) t =
        deriv (deriv g) (s t) * deriv s t * deriv s t + deriv g (s t) * deriv (deriv s) t := by
      have hA : HasDerivAt (fun t => deriv g (s t)) (deriv (deriv g) (s t) * deriv s t) t :=
        (hg'd (s t)).hasDerivAt.comp t (hsd t).hasDerivAt
      exact (hA.mul (hs'd t).hasDerivAt).deriv
    rw [this]
    refine (abs_add_le _ _).trans ?_
    simp only [abs_mul]
    have c1 := hg1 (s t); have c2 := hg2' (s t); have c3 := hs1 t; have c4 := hs2' t
    have p1 : 0 ≤ |deriv g (s t)| := abs_nonneg _
    have p2 : 0 ≤ |deriv s t| := abs_nonneg _
    have p3 : 0 ≤ |deriv (deriv g) (s t)| := abs_nonneg _
    have p4 : 0 ≤ |deriv (deriv s) t| := abs_nonneg _
    have n1 : 0 ≤ Cs1 := p2.trans c3
    have n2 : 0 ≤ Cg2 := p3.trans c2
    have q1 : |deriv (deriv g) (s t)| * |deriv s t| * |deriv s t| ≤ Cg2 * Cs1 * Cs1 :=
      mul_le_mul (mul_le_mul c2 c3 p2 n2) c3 p2 (mul_nonneg n2 n1)
    have q2 : |deriv g (s t)| * |deriv (deriv s) t| ≤ Cg1 * Cs2 :=
      mul_le_mul c1 c4 p4 (p1.trans c1)
    linarith

lemma B2.affine {g : ℝ → ℝ} (hg : B2 g) (a b : ℝ) : B2 (fun t => a + b * g t) := by
  obtain ⟨hg2, ⟨C1, h1⟩, ⟨C2, h2⟩⟩ := hg
  have hgd : Differentiable ℝ g := hg2.differentiable (by norm_num)
  have hd : deriv (fun t => a + b * g t) = fun t => b * deriv g t := by
    funext t; rw [deriv_const_add, deriv_const_mul _ (hgd t)]
  refine ⟨contDiff_const.add (contDiff_const.mul hg2), ⟨|b| * C1, fun t => ?_⟩,
    ⟨|b| * C2, fun t => ?_⟩⟩
  · rw [hd]; simp only [abs_mul]; gcongr; exact h1 t
  · rw [hd, deriv_const_mul_field]; simp only [abs_mul]; gcongr; exact h2 t

lemma B2.smoothTransition : B2 Real.smoothTransition := by
  have hc : ContDiff ℝ 2 Real.smoothTransition := Real.smoothTransition.contDiff
  have h1 : ContDiff ℝ 1 (deriv Real.smoothTransition) :=
    ((contDiff_succ_iff_deriv (n := 1)).1 hc).2.2
  have h0 : ∀ x, x < 0 → deriv Real.smoothTransition x = 0 := by
    intro x hx
    have : Real.smoothTransition =ᶠ[nhds x] fun _ => 0 :=
      Filter.eventually_of_mem (Iio_mem_nhds hx) fun y hy => Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [this.deriv_eq]; simp
  have h1' : ∀ x, 1 < x → deriv Real.smoothTransition x = 0 := by
    intro x hx
    have : Real.smoothTransition =ᶠ[nhds x] fun _ => 1 :=
      Filter.eventually_of_mem (Ioi_mem_nhds hx) fun y hy => Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [this.deriv_eq]; simp
  have hcs : ∀ x, x ∉ Set.Icc (0:ℝ) 1 → deriv Real.smoothTransition x = 0 := by
    intro x hx
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · exact h0 x hx
    · exact h1' x hx
  have hcs2 : ∀ x, x ∉ Set.Icc (0:ℝ) 1 → deriv (deriv Real.smoothTransition) x = 0 := by
    intro x hx
    have hxo : IsOpen (Set.Icc (0:ℝ) 1)ᶜ := isClosed_Icc.isOpen_compl
    have : deriv Real.smoothTransition =ᶠ[nhds x] fun _ => 0 :=
      Filter.eventually_of_mem (hxo.mem_nhds hx) fun y hy => hcs y hy
    rw [this.deriv_eq]; simp
  refine ⟨hc, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := h1.continuous.bounded_above_of_compact_support
      (HasCompactSupport.intro isCompact_Icc hcs)
    exact ⟨C, fun t => by simpa using hC t⟩
  · obtain ⟨C, hC⟩ := (h1.continuous_deriv (by norm_num)).bounded_above_of_compact_support
      (HasCompactSupport.intro isCompact_Icc hcs2)
    exact ⟨C, fun t => by simpa using hC t⟩

lemma psi_eq (t : ℝ) : gaussianPDFReal 0 1 t = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2) / 2) := by
  simp [gaussianPDFReal]

lemma psi_contDiff : ContDiff ℝ 2 (gaussianPDFReal 0 1) := by
  have : gaussianPDFReal 0 1 = fun t => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2) / 2) :=
    funext psi_eq
  rw [this]
  fun_prop

lemma psi_deriv (t : ℝ) : deriv (gaussianPDFReal 0 1) t = -t * gaussianPDFReal 0 1 t := by
  have : gaussianPDFReal 0 1 = fun t => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2) / 2) :=
    funext psi_eq
  rw [this]
  have h : HasDerivAt (fun t : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2) / 2))
      ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-(t ^ 2) / 2) * (-(2 * t) / 2))) t := by
    refine HasDerivAt.const_mul _ ?_
    refine HasDerivAt.exp ?_
    have := ((hasDerivAt_pow 2 t).neg).div_const 2
    simpa using this
  rw [h.deriv]; ring

lemma psi_le_one (t : ℝ) : gaussianPDFReal 0 1 t ≤ 1 := by
  rw [psi_eq]
  have h1 : 1 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.one_le_sqrt]; linarith [Real.pi_gt_three]
  have h2 : Real.exp (-(t ^ 2) / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg t]
  calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2) / 2) ≤ 1 * 1 :=
        mul_le_mul (inv_le_one_of_one_le₀ h1) h2 (Real.exp_pos _).le zero_le_one
    _ = 1 := one_mul 1

lemma abs_t_psi_le (t : ℝ) : |t| * gaussianPDFReal 0 1 t ≤ 1 := by
  rw [psi_eq]
  have h1 : 1 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.one_le_sqrt]; linarith [Real.pi_gt_three]
  have h2 : |t| * Real.exp (-(t ^ 2) / 2) ≤ 1 := by
    have e : Real.exp (t ^ 2 / 2) ≥ 1 + t ^ 2 / 2 := by linarith [Real.add_one_le_exp (t ^ 2 / 2)]
    have : Real.exp (-(t ^ 2) / 2) = (Real.exp (t ^ 2 / 2))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [this, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    nlinarith [sq_abs t, abs_nonneg t, sq_nonneg (|t| - 1)]
  calc |t| * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2) / 2))
      = (Real.sqrt (2 * Real.pi))⁻¹ * (|t| * Real.exp (-(t ^ 2) / 2)) := by ring
    _ ≤ 1 * 1 := mul_le_mul (inv_le_one_of_one_le₀ h1) h2 (by positivity) zero_le_one
    _ = 1 := one_mul 1

lemma Phi_eq_integral (t : ℝ) : Phi t = ∫ x in Set.Iic t, gaussianPDFReal 0 1 x := by
  unfold Phi
  rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral _ (by norm_num)]
  rw [ENNReal.toReal_ofReal (integral_nonneg fun x => gaussianPDFReal_nonneg _ _ _)]

lemma psi_integrable : Integrable (gaussianPDFReal 0 1) := integrable_gaussianPDFReal 0 1

lemma Phi_eq_add (t : ℝ) : Phi t = Phi 0 + ∫ x in (0:ℝ)..t, gaussianPDFReal 0 1 x := by
  rw [Phi_eq_integral, Phi_eq_integral, ← intervalIntegral.integral_Iic_sub_Iic psi_integrable.integrableOn
    psi_integrable.integrableOn]
  ring

lemma Phi_hasDerivAt (t : ℝ) : HasDerivAt Phi (gaussianPDFReal 0 1 t) t := by
  have : Phi = fun t => Phi 0 + ∫ x in (0:ℝ)..t, gaussianPDFReal 0 1 x := funext Phi_eq_add
  rw [this]
  refine HasDerivAt.const_add _ ?_
  exact intervalIntegral.integral_hasDerivAt_right (psi_integrable.intervalIntegrable)
    (psi_contDiff.continuous.stronglyMeasurableAtFilter _ _) psi_contDiff.continuous.continuousAt

lemma Phi_deriv : deriv Phi = gaussianPDFReal 0 1 := funext fun t => (Phi_hasDerivAt t).deriv

lemma B2_Phi : B2 Phi := by
  have hc : ContDiff ℝ 2 Phi := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
    refine ⟨fun t => (Phi_hasDerivAt t).differentiableAt, by simp, ?_⟩
    rw [Phi_deriv]
    exact psi_contDiff.of_le (by norm_num)
  refine ⟨hc, ⟨1, fun t => ?_⟩, ⟨1, fun t => ?_⟩⟩
  · rw [Phi_deriv, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]; exact psi_le_one t
  · rw [Phi_deriv, psi_deriv, abs_mul, abs_neg, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]; exact abs_t_psi_le t

lemma Phi_strictMono : StrictMono Phi :=
  strictMono_of_deriv_pos fun t => by
    rw [Phi_deriv]; exact gaussianPDFReal_pos _ _ _ (by norm_num)

lemma Phi_monotone : Monotone Phi := Phi_strictMono.monotone

lemma Phi_continuous : Continuous Phi :=
  continuous_iff_continuousAt.2 fun t => (Phi_hasDerivAt t).continuousAt


section chain
variable {n : ℕ}

lemma D_chain (G : (Fin n → ℝ) → ℝ) (hG : Differentiable ℝ G) (u : Fin n → ℝ → ℝ)
    (hu : ∀ i, Differentiable ℝ (u i)) (j : Fin n) (z : Fin n → ℝ) :
    D j (fun z => G (fun i => u i (z i))) z = deriv (u j) (z j) * D j G (fun i => u i (z i)) := by
  have hQ : HasFDerivAt (fun z : Fin n → ℝ => fun i => u i (z i))
      (ContinuousLinearMap.pi fun i =>
        (deriv (u i) (z i)) • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) z := by
    refine hasFDerivAt_pi'.2 fun i => ?_
    exact (hu i (z i)).hasDerivAt.comp_hasFDerivAt z (hasFDerivAt_apply i z)
  have h : HasFDerivAt (fun z : Fin n → ℝ => G (fun i => u i (z i))) _ z :=
    (hG (fun i => u i (z i))).hasFDerivAt.comp z hQ
  unfold D
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  have : (ContinuousLinearMap.pi fun i =>
        (deriv (u i) (z i)) • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) (Pi.single j (1 : ℝ))
      = deriv (u j) (z j) • (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
    ext i
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [this, map_smul, smul_eq_mul]

lemma D_eval (ψ : ℝ → ℝ) (hψ : Differentiable ℝ ψ) (i j : Fin n) (z : Fin n → ℝ) :
    D i (fun z : Fin n → ℝ => ψ (z j)) z = if i = j then deriv ψ (z j) else 0 := by
  have h : HasFDerivAt (fun z : Fin n → ℝ => ψ (z j)) _ z :=
    (hψ (z j)).hasDerivAt.comp_hasFDerivAt z
      (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt
  unfold D
  rw [h.fderiv]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

lemma D_mul (a b : (Fin n → ℝ) → ℝ) (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) (i : Fin n)
    (z : Fin n → ℝ) : D i (fun z => a z * b z) z = D i a z * b z + a z * D i b z := by
  unfold D
  rw [fderiv_fun_mul (ha z) (hb z)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma D_chain2 (G : (Fin n → ℝ) → ℝ) (hG : ContDiff ℝ 2 G) (u : Fin n → ℝ → ℝ)
    (hu : ∀ i, ContDiff ℝ 2 (u i)) (i j : Fin n) (z : Fin n → ℝ) :
    D i (D j (fun z => G (fun l => u l (z l)))) z =
      (if i = j then deriv (deriv (u j)) (z j) * D j G (fun l => u l (z l)) else 0) +
      deriv (u j) (z j) * (deriv (u i) (z i) * D i (D j G) (fun l => u l (z l))) := by
  have hud : ∀ l, Differentiable ℝ (u l) := fun l => (hu l).differentiable (by norm_num)
  have hu'd : ∀ l, Differentiable ℝ (deriv (u l)) := fun l =>
    ((contDiff_succ_iff_deriv (n := 1)).1 (hu l)).2.2.differentiable (by norm_num)
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hDG : Differentiable ℝ (D j G) :=
    (D_contDiff G hG j).differentiable (by norm_num)
  have e : D j (fun z => G (fun l => u l (z l))) =
      fun z => deriv (u j) (z j) * D j G (fun l => u l (z l)) :=
    funext fun z => D_chain G hGd u hud j z
  rw [e, D_mul _ _ ?_ ?_, D_eval _ (hu'd j), D_chain (D j G) hDG u hud i z]
  · by_cases hij : i = j <;> simp [hij]
  · exact (hu'd j).comp (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).differentiable
  · exact hDG.comp (differentiable_pi.2 fun l => (hud l).comp
      (ContinuousLinearMap.proj l : (Fin n → ℝ) →L[ℝ] ℝ).differentiable)

end chain

section smoothing
open NonmonotoneSubmod.Shared
variable {n : ℕ}

lemma F_contDiff (f : Finset (Fin n) → ℝ) {k : WithTop ℕ∞} : ContDiff ℝ k (F f) := by
  unfold F
  refine ContDiff.sum fun S _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  by_cases h : i ∈ S
  · simp only [h, if_true]; exact contDiff_apply ℝ ℝ i
  · simp only [h, if_false]; exact contDiff_const.sub (contDiff_apply ℝ ℝ i)

lemma F_abs_le (f : Finset (Fin n) → ℝ) (y : Fin n → ℝ) (hy : ∀ i, y i ∈ Set.Icc (0:ℝ) 1) :
    |F f y| ≤ ∑ S, |f S| := by
  unfold F
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S _ => ?_)
  rw [abs_mul]
  have : |∏ i, (if i ∈ S then y i else 1 - y i)| ≤ 1 := by
    rw [Finset.abs_prod]
    refine Finset.prod_le_one (fun i _ => abs_nonneg _) fun i _ => ?_
    have := hy i
    by_cases h : i ∈ S
    · simp only [h, if_true]; rw [abs_of_nonneg this.1]; exact this.2
    · simp only [h, if_false]; rw [abs_of_nonneg (by linarith [this.2])]; linarith [this.1]
  calc |f S| * |∏ i, (if i ∈ S then y i else 1 - y i)| ≤ |f S| * 1 :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = |f S| := mul_one _

lemma F_indicator (f : Finset (Fin n) → ℝ) (R : Finset (Fin n)) :
    F f (fun i => if i ∈ R then (1:ℝ) else 0) = f R := by
  unfold F
  rw [Finset.sum_eq_single R]
  · have : ∏ i : Fin n, (if i ∈ R then (if i ∈ R then (1:ℝ) else 0) else 1 - (if i ∈ R then (1:ℝ) else 0)) = 1 :=
      Finset.prod_eq_one fun i _ => by by_cases h : i ∈ R <;> simp [h]
    rw [this, mul_one]
  · intro S _ hS
    have : ∏ i : Fin n, (if i ∈ S then (if i ∈ R then (1:ℝ) else 0) else 1 - (if i ∈ R then (1:ℝ) else 0)) = 0 := by
      obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ R) := by
        by_contra hc
        exact hS (Finset.ext fun i => by_contra fun h => hc ⟨i, h⟩)
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      by_cases h1 : i ∈ S <;> by_cases h2 : i ∈ R <;> simp_all
    rw [this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ R) h

noncomputable def uu (x : Fin n → ℝ) (ε : ℝ) (i : Fin n) (t : ℝ) : ℝ :=
  Real.smoothTransition (1 + (Phi t - (1 - x i)) / ε)

lemma uu_B2 (x : Fin n → ℝ) {ε : ℝ} (i : Fin n) : B2 (uu x ε i) := by
  have h := B2.comp B2.smoothTransition (B2.affine B2_Phi (1 - (1 - x i) / ε) (1 / ε))
  convert h using 2
  unfold uu
  congr 1
  ring

lemma uu_nonneg (x : Fin n → ℝ) (ε : ℝ) (i : Fin n) (t : ℝ) : 0 ≤ uu x ε i t :=
  Real.smoothTransition.nonneg _

lemma uu_le_one (x : Fin n → ℝ) (ε : ℝ) (i : Fin n) (t : ℝ) : uu x ε i t ≤ 1 :=
  Real.smoothTransition.le_one _

lemma uu_mono (x : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) (i : Fin n) : Monotone (uu x ε i) := by
  intro a b hab
  unfold uu
  refine Real.smoothTransition.monotone ?_
  have := Phi_monotone hab
  have : (Phi a - (1 - x i)) / ε ≤ (Phi b - (1 - x i)) / ε := by gcongr
  linarith

lemma uu_deriv_nonneg (x : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) (i : Fin n) (t : ℝ) :
    0 ≤ deriv (uu x ε i) t := (uu_mono x hε i).deriv_nonneg

end smoothing

section hhprops
open NonmonotoneSubmod.Shared
variable {n : ℕ}

noncomputable def hh (f : Finset (Fin n) → ℝ) (x : Fin n → ℝ) (ε : ℝ) (z : Fin n → ℝ) : ℝ :=
  F f (fun i => uu x ε i (z i))

lemma Q_mem (x : Fin n → ℝ) (ε : ℝ) (z : Fin n → ℝ) (i : Fin n) :
    uu x ε i (z i) ∈ Set.Icc (0:ℝ) 1 := ⟨uu_nonneg _ _ _ _, uu_le_one _ _ _ _⟩

lemma cube_bound (f : Finset (Fin n) → ℝ) :
    ∃ M : ℝ, ∀ y : Fin n → ℝ, (∀ i, y i ∈ Set.Icc (0:ℝ) 1) →
      (∀ i, |D i (F f) y| ≤ M) ∧ (∀ i j, |D j (D i (F f)) y| ≤ M) := by
  have hG : ContDiff ℝ 3 (F f) := F_contDiff f
  have hc1 : ∀ i, Continuous (D i (F f)) := fun i =>
    (D_contDiff (F f) (hG.of_le (by norm_num)) i).continuous
  have hc2 : ∀ i j, Continuous (D j (D i (F f))) := fun i j =>
    (((D_contDiff (F f) (hG.of_le (by norm_num)) i).continuous_fderiv one_ne_zero).clm_apply
      continuous_const)
  let K : (Fin n → ℝ) → ℝ := fun y => ∑ i, |D i (F f) y| + ∑ i, ∑ j, |D j (D i (F f)) y|
  have hK : Continuous K := by
    refine Continuous.add (continuous_finsetSum _ fun i _ => (hc1 i).abs)
      (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (hc2 i j).abs)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := 1)).exists_bound_of_continuousOn hK.continuousOn
  refine ⟨M, fun y hy => ?_⟩
  have hy' : y ∈ Set.Icc (0 : Fin n → ℝ) 1 := ⟨fun i => (hy i).1, fun i => (hy i).2⟩
  have hKM : K y ≤ M := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM y hy')
  have e1 : ∀ i, |D i (F f) y| ≤ K y := fun i => by
    have : |D i (F f) y| ≤ ∑ i, |D i (F f) y| :=
      Finset.single_le_sum (f := fun i => |D i (F f) y|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have : 0 ≤ ∑ i, ∑ j, |D j (D i (F f)) y| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    simp only [K]; linarith
  have e2 : ∀ i j, |D j (D i (F f)) y| ≤ K y := fun i j => by
    have h1 : |D j (D i (F f)) y| ≤ ∑ j, |D j (D i (F f)) y| :=
      Finset.single_le_sum (f := fun j => |D j (D i (F f)) y|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 : ∑ j, |D j (D i (F f)) y| ≤ ∑ i, ∑ j, |D j (D i (F f)) y| :=
      Finset.single_le_sum (f := fun i => ∑ j, |D j (D i (F f)) y|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have : 0 ≤ ∑ i, |D i (F f) y| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    simp only [K]; linarith
  exact ⟨fun i => (e1 i).trans hKM, fun i j => (e2 i j).trans hKM⟩

lemma u_bounds (x : Fin n → ℝ) (ε : ℝ) :
    ∃ B : ℝ, ∀ i t, |deriv (uu x ε i) t| ≤ B ∧ |deriv (deriv (uu x ε i)) t| ≤ B := by
  have h : ∀ i, ∃ b : ℝ, ∀ t, |deriv (uu x ε i) t| ≤ b ∧ |deriv (deriv (uu x ε i)) t| ≤ b := by
    intro i
    obtain ⟨_, ⟨b1, h1⟩, ⟨b2, h2⟩⟩ := uu_B2 x (ε := ε) i
    exact ⟨max b1 b2, fun t => ⟨(h1 t).trans (le_max_left _ _), (h2 t).trans (le_max_right _ _)⟩⟩
  choose b hb using h
  refine ⟨∑ i, |b i|, fun i t => ?_⟩
  have : |b i| ≤ ∑ i, |b i| :=
    Finset.single_le_sum (f := fun i => |b i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  exact ⟨((hb i t).1.trans (le_abs_self _)).trans this, ((hb i t).2.trans (le_abs_self _)).trans this⟩

lemma hh_contDiff (f : Finset (Fin n) → ℝ) (x : Fin n → ℝ) {ε : ℝ} : ContDiff ℝ 2 (hh f x ε) := by
  unfold hh
  refine (F_contDiff f).comp (contDiff_pi.2 fun i => ?_)
  exact (uu_B2 x (ε := ε) i).1.comp (contDiff_apply ℝ ℝ i)

lemma hh_bound (f : Finset (Fin n) → ℝ) (x : Fin n → ℝ) (ε : ℝ) (z : Fin n → ℝ) :
    |hh f x ε z| ≤ ∑ S, |f S| := F_abs_le f _ fun i => Q_mem x ε z i

lemma hh_D_bound (f : Finset (Fin n) → ℝ) (x : Fin n → ℝ) (ε : ℝ) :
    ∃ C1 : ℝ, ∀ z i, |D i (hh f x ε) z| ≤ C1 := by
  obtain ⟨M, hM⟩ := cube_bound f
  obtain ⟨B, hB⟩ := u_bounds x ε
  refine ⟨B * M, fun z i => ?_⟩
  have hud : ∀ l, Differentiable ℝ (uu x ε l) := fun l => (uu_B2 x (ε := ε) l).1.differentiable (by norm_num)
  have := D_chain (F f) ((F_contDiff f (k := 2)).differentiable (by norm_num)) (uu x ε) hud i z
  unfold hh
  rw [this, abs_mul]
  exact mul_le_mul (hB i _).1 ((hM _ fun l => Q_mem x ε z l).1 i) (abs_nonneg _)
    ((abs_nonneg _).trans (hB i 0).1)

lemma hh_D2_bound (f : Finset (Fin n) → ℝ) (x : Fin n → ℝ) (ε : ℝ) :
    ∃ C2 : ℝ, ∀ z i j, |D j (D i (hh f x ε)) z| ≤ C2 := by
  obtain ⟨M, hM⟩ := cube_bound f
  obtain ⟨B, hB⟩ := u_bounds x ε
  refine ⟨B * M + B * (B * M), fun z i j => ?_⟩
  have hu : ∀ l, ContDiff ℝ 2 (uu x ε l) := fun l => (uu_B2 x (ε := ε) l).1
  have := D_chain2 (F f) (F_contDiff f) (uu x ε) hu j i z
  unfold hh
  rw [this]
  have hQ := hM _ fun l => Q_mem x ε z l
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hQ.1 i)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB i 0).1
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · split_ifs
    · rw [abs_mul]
      exact mul_le_mul (hB _ _).2 (hQ.1 _) (abs_nonneg _) hB0
    · simpa using mul_nonneg hB0 hM0
  · rw [abs_mul, abs_mul]
    exact mul_le_mul (hB _ _).1 (mul_le_mul (hB _ _).1 (hQ.2 _ _) (abs_nonneg _) hB0) (by positivity) hB0

lemma hh_neg (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f)
    (x : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) (z : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) :
    D j (D i (hh f x ε)) z ≤ 0 := by
  have hu : ∀ l, ContDiff ℝ 2 (uu x ε l) := fun l => (uu_B2 x (ε := ε) l).1
  have := D_chain2 (F f) (F_contDiff f) (uu x ε) hu j i z
  unfold hh
  rw [this, if_neg (Ne.symm hij), zero_add]
  have h2 := (eq_2_second_partials f hf0 hf (fun l => uu x ε l (z l)) (fun l => Q_mem x ε z l) j i).2.2.1
  have h3 : D j (D i (F f)) (fun l => uu x ε l (z l)) ≤ 0 := h2
  have a1 := uu_deriv_nonneg x hε i (z i)
  have a2 := uu_deriv_nonneg x hε j (z j)
  exact mul_nonpos_of_nonneg_of_nonpos a1 (mul_nonpos_of_nonneg_of_nonpos a2 h3)

end hhprops

section limit
open NonmonotoneSubmod.Shared
variable {n : ℕ}

lemma null_level {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) (hSi : ∀ i, S i i = 1)
    (i : Fin n) (c : ℝ) :
    multivariateGaussian 0 S {g : E n | Phi (g i) = c} = 0 := by
  have hmp := measurePreserving_eval_multivariateGaussian (μ := (0 : E n)) hS (i := i)
  have hm : MeasurableSet {t : ℝ | Phi t = c} :=
    (isClosed_eq Phi_continuous continuous_const).measurableSet
  have : {g : E n | Phi (g i) = c} = (fun g : E n => g i) ⁻¹' {t | Phi t = c} := rfl
  rw [this, hmp.measure_preimage hm.nullMeasurableSet]
  have h1 : ((S i i).toNNReal) = 1 := by rw [hSi]; simp
  simp only [h1, PiLp.zero_apply]
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  refine Set.Subsingleton.measure_zero ?_ _
  intro a ha b hb
  exact Phi_strictMono.injective (ha.trans hb.symm)

lemma ptwise (f : Finset (Fin n) → ℝ) (x : Fin n → ℝ) (g : E n)
    (hg : ∀ i, Phi (g i) ≠ 1 - x i) :
    Filter.Tendsto (fun k : ℕ => hh f x (1 / ((k : ℝ) + 1)) (fun i => g i)) Filter.atTop
      (nhds (f (Finset.univ.filter fun i => 1 - x i ≤ Phi (g i)))) := by
  have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hev : ∀ᶠ k : ℕ in Filter.atTop, ∀ i, uu x (1 / ((k : ℝ) + 1)) i (g i) =
      if i ∈ (Finset.univ.filter fun i => 1 - x i ≤ Phi (g i)) then 1 else 0 := by
    rw [Filter.eventually_all]
    intro i
    by_cases h : 1 - x i ≤ Phi (g i)
    · have hlt : 1 - x i < Phi (g i) := lt_of_le_of_ne h (fun e => hg i e.symm)
      refine Filter.Eventually.of_forall fun k => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, h, if_true]
      unfold uu
      apply Real.smoothTransition.one_of_one_le
      have : 0 ≤ (Phi (g i) - (1 - x i)) / (1 / ((k : ℝ) + 1)) := by
        apply div_nonneg (by linarith) (by positivity)
      linarith
    · have hlt : Phi (g i) < 1 - x i := not_le.1 h
      have hδ : 0 < 1 - x i - Phi (g i) := by linarith
      filter_upwards [h0.eventually (gt_mem_nhds hδ)] with k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, h, if_false]
      unfold uu
      apply Real.smoothTransition.zero_of_nonpos
      have hpos : 0 < 1 / ((k : ℝ) + 1) := by positivity
      have : (Phi (g i) - (1 - x i)) / (1 / ((k : ℝ) + 1)) ≤ -1 := by
        rw [div_le_iff₀ hpos]; linarith
      linarith
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev] with k hk
  unfold hh
  rw [show (fun i => uu x (1 / ((k : ℝ) + 1)) i (g i)) =
      (fun i => if i ∈ (Finset.univ.filter fun i => 1 - x i ≤ Phi (g i)) then (1:ℝ) else 0)
      from funext hk, F_indicator]

theorem limit_semidefExt (f : Finset (Fin n) → ℝ) (x : Fin n → ℝ)
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) (hSi : ∀ i, S i i = 1) :
    Filter.Tendsto (fun k : ℕ => ∫ g : E n, hh f x (1 / ((k : ℝ) + 1)) (fun i => g i)
        ∂(multivariateGaussian 0 S)) Filter.atTop (nhds (semidefExt f x S)) := by
  unfold semidefExt
  refine tendsto_integral_of_dominated_convergence (fun _ => ∑ T, |f T|) (fun k => ?_)
    (integrable_const _) (fun k => ae_of_all _ fun g => ?_) ?_
  · refine Continuous.aestronglyMeasurable ?_
    exact (hh_contDiff f x).continuous.comp
      (continuous_pi fun i => (EuclideanSpace.proj i : E n →L[ℝ] ℝ).continuous)
  · rw [Real.norm_eq_abs]; exact hh_bound f x _ _
  · have : ∀ᵐ g ∂(multivariateGaussian 0 S), ∀ i, Phi (g i) ≠ 1 - x i := by
      rw [ae_all_iff]
      intro i
      have := measure_eq_zero_iff_ae_notMem.1 (null_level hS hSi i (1 - x i))
      filter_upwards [this] with g hg
      exact hg
    filter_upwards [this] with g hg
    exact ptwise f x g hg

end limit
end UniversalSubmod.Dev.Thm23

namespace UniversalSubmod

open NonmonotoneSubmod.Shared

theorem chk_theorem_2_3 {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f)
    (S S' : Matrix (Fin n) (Fin n) ℝ) (hS : CorrMatrix S) (hS' : CorrMatrix S')
    (hle : ∀ i j, i ≠ j → S i j ≤ S' i j)
    (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    semidefExt f x S' ≤ semidefExt f x S := by
  refine le_of_tendsto_of_tendsto' (Dev.Thm23.limit_semidefExt f x hS'.1 hS'.2)
    (Dev.Thm23.limit_semidefExt f x hS.1 hS.2) fun k => ?_
  obtain ⟨C1, hC1⟩ := Dev.Thm23.hh_D_bound f x (1 / ((k : ℝ) + 1))
  obtain ⟨C2, hC2⟩ := Dev.Thm23.hh_D2_bound f x (1 / ((k : ℝ) + 1))
  exact Dev.Thm23.comparison hS.1 hS'.1 hle (fun i => by rw [hS.2, hS'.2])
    (Dev.Thm23.hh f x (1 / ((k : ℝ) + 1))) (Dev.Thm23.hh_contDiff f x) (∑ T, |f T|)
    (Dev.Thm23.hh_bound f x _) C1 hC1 C2 hC2
    (fun z i j hij => Dev.Thm23.hh_neg f hf0 hf x (by positivity) z i j hij)

end UniversalSubmod
end

theorem solution : type_of% @UniversalSubmod.chk_theorem_2_3 := @UniversalSubmod.chk_theorem_2_3
