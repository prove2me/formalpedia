-- Prove2me | solution 1 for RandomGradFree.Nonsmooth.gaussian_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:46:05.904271+00:00
-- url     : https://prove2.me/submissions/5e9927f3-bcf6-4940-99eb-5750de967726

import Mathlib
import Definitions.Def_RandomGradFree_Shared_moment
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace AGaussianMoment

lemma density_exp (t x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (t * x ^ 2) =
      (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(1 / 2 - t) * x ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2 <;> ring

lemma scalar_exp_integrable {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (t * x ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff (measurable_gaussianPDF _ _) (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF]
  simp_rw [mul_comm (Real.exp _), density_exp]
  exact (integrable_exp_neg_mul_sq (by linarith : 0 < 1 / 2 - t)).const_mul _

lemma scalar_exp_integral {t : ℝ} (ht : t < 1 / 2) :
    (∫ x : ℝ, Real.exp (t * x ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  simp_rw [density_exp]
  rw [integral_const_mul, integral_gaussian]
  have hd : 0 < 1 - 2 * t := by linarith
  have hp : 0 < 2 * Real.pi := by positivity
  have hdiv : Real.pi / (1 / 2 - t) = (2 * Real.pi) / (1 - 2 * t) := by
    field_simp
    <;> ring
  rw [hdiv, Real.sqrt_div hp.le]
  field_simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma norm_exp_prod (t : ℝ) (z : Fin (Module.finrank ℝ E) → ℝ) :
    Real.exp (t * ‖∑ i, z i • stdOrthonormalBasis ℝ E i‖ ^ 2) =
      ∏ i, Real.exp (t * z i ^ 2) := by
  have hs : ‖∑ i, z i • stdOrthonormalBasis ℝ E i‖ ^ 2 = ∑ i, z i ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, (stdOrthonormalBasis ℝ E).orthonormal.inner_sum]
    simp [pow_two]
  rw [hs, Finset.mul_sum, Real.exp_sum]

lemma exp_integrable {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun u : E => Real.exp (t * ‖u‖ ^ 2)) (stdGaussian E) := by
  classical
  rw [stdGaussian_eq_map_pi_orthonormalBasis (stdOrthonormalBasis ℝ E),
    integrable_map_measure (by fun_prop) (Measurable.aemeasurable (by fun_prop))]
  simp only [Function.comp_def, norm_exp_prod]
  exact Integrable.fintype_prod (fun _ => scalar_exp_integrable ht)

lemma exp_integral {t : ℝ} (ht : t < 1 / 2) :
    (∫ u : E, Real.exp (t * ‖u‖ ^ 2) ∂stdGaussian E) =
      (Real.sqrt (1 - 2 * t))⁻¹ ^ Module.finrank ℝ E := by
  classical
  rw [stdGaussian_eq_map_pi_orthonormalBasis (stdOrthonormalBasis ℝ E),
    integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  simp_rw [norm_exp_prod]
  rw [integral_fintype_prod_eq_prod (fun _ (x : ℝ) => Real.exp (t * x ^ 2))]
  simp [scalar_exp_integral ht]

lemma moment_integrable {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun u : E => ‖u‖ ^ p) (stdGaussian E) := by
  simpa [ENNReal.toReal_ofReal hp] using
    (IsGaussian.memLp_id (stdGaussian E) (ENNReal.ofReal p) (by simp)).integrable_norm_rpow'

theorem moment_two {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    ∫ u, ‖u‖ ^ 2 ∂(stdGaussian E) = Module.finrank ℝ E := by
  set b := stdOrthonormalBasis ℝ E
  have hmem : MemLp (id : E → E) 2 (stdGaussian E) := IsGaussian.memLp_two_id
  have hone : ∀ i, ∫ u, ⟪b i, u⟫ ^ 2 ∂(stdGaussian E) = 1 := by
    intro i
    have h := covarianceBilin_apply hmem (b i) (b i)
    rw [covarianceBilin_stdGaussian] at h
    have hm : (stdGaussian E)[id] = 0 := by simp
    simp only [hm, sub_zero] at h
    change ⟪b i, b i⟫ = _ at h
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i] at h
    simp only [one_pow] at h
    rw [h]
    congr 1
    ext u
    ring
  have hint : ∀ i, Integrable (fun u => ⟪b i, u⟫ ^ 2) (stdGaussian E) := by
    intro i
    have : MemLp (fun u : E => ⟪b i, u⟫) 2 (stdGaussian E) :=
      (innerSL ℝ (b i)).comp_memLp' hmem
    exact this.integrable_sq
  calc ∫ u, ‖u‖ ^ 2 ∂(stdGaussian E)
      = ∫ u, ∑ i, ⟪b i, u⟫ ^ 2 ∂(stdGaussian E) := by
        congr 1; ext u; rw [b.sum_sq_inner_right]
    _ = ∑ i, ∫ u, ⟪b i, u⟫ ^ 2 ∂(stdGaussian E) := integral_finsetSum _ (fun i _ => hint i)
    _ = Module.finrank ℝ E := by simp [hone]


lemma sq_rpow (x : ℝ) (hx : 0 ≤ x) (p : ℝ) : (x ^ 2) ^ (p / 2) = x ^ p := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

lemma low_moment {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) :
    (∫ u : E, ‖u‖ ^ p ∂stdGaussian E) ≤ (Module.finrank ℝ E : ℝ) ^ (p / 2) := by
  have hi := moment_integrable (E := E) hp
  have hi2 : Integrable (fun u : E => ‖u‖ ^ (2 : ℕ)) (stdGaussian E) := by
    simpa using moment_integrable (E := E) (p := 2) (by norm_num)
  have h := (Real.concaveOn_rpow (by linarith : 0 ≤ p / 2) (by linarith : p / 2 ≤ 1)).le_map_integral
    (Real.continuous_rpow_const (by linarith : 0 ≤ p / 2)).continuousOn
    isClosed_Ici (ae_of_all (stdGaussian E) (fun u : E => sq_nonneg ‖u‖)) hi2
    (by simpa only [Function.comp_def, sq_rpow _ (norm_nonneg _) p] using hi)
  simpa only [moment_two, sq_rpow _ (norm_nonneg _) p] using h

lemma lower_moment {p : ℝ} (hp : 2 ≤ p) :
    (Module.finrank ℝ E : ℝ) ^ (p / 2) ≤ (∫ u : E, ‖u‖ ^ p ∂stdGaussian E) := by
  have hi := moment_integrable (E := E) (p := p) (by linarith)
  have hi2 : Integrable (fun u : E => ‖u‖ ^ (2 : ℕ)) (stdGaussian E) := by
    simpa using moment_integrable (E := E) (p := 2) (by norm_num)
  have h := (convexOn_rpow (by linarith : 1 ≤ p / 2)).map_integral_le
    (Real.continuous_rpow_const (by linarith : 0 ≤ p / 2)).continuousOn
    isClosed_Ici (ae_of_all (stdGaussian E) (fun u : E => sq_nonneg ‖u‖)) hi2
    (by simpa only [Function.comp_def, sq_rpow _ (norm_nonneg _) p] using hi)
  simpa only [moment_two, sq_rpow _ (norm_nonneg _) p] using h


lemma pointwise_bound {x a p : ℝ} (hx : 0 ≤ x) (ha : 0 < a) (hp : 0 < p) :
    x ^ p ≤ a ^ (p / 2) * Real.exp (-p / 2) * Real.exp (p / (2 * a) * x ^ 2) := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp only [Real.zero_rpow hp.ne']
    positivity
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos ha, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := Real.log_le_sub_one_of_pos (div_pos (sq_pos_of_pos hx) ha)
  rw [Real.log_div (pow_ne_zero 2 hx.ne') ha.ne', Real.log_pow] at h
  have h' := mul_le_mul_of_nonneg_right h (show 0 ≤ p / 2 by positivity)
  have he : (x ^ 2 / a - 1) * (p / 2) = -p / 2 + p / (2 * a) * x ^ 2 := by ring
  rw [he] at h'
  nlinarith

lemma mgf_bound (n : ℕ) {p : ℝ} (hn : 0 < (n : ℝ)) (hp : 0 < p) :
    (Real.sqrt (1 - 2 * (p / (2 * (n + p)))))⁻¹ ^ n ≤ Real.exp (p / 2) := by
  have ha : 0 < (n : ℝ) + p := by positivity
  have hd : 1 - 2 * (p / (2 * (n + p))) = (n : ℝ) / (n + p) := by
    field_simp
    <;> ring
  rw [hd]
  have hpos : 0 < (Real.sqrt ((n : ℝ) / (n + p)))⁻¹ ^ n := by positivity
  rw [← Real.exp_log hpos, Real.exp_le_exp]
  rw [Real.log_pow, Real.log_inv, Real.log_sqrt (by positivity),
    Real.log_div hn.ne' ha.ne']
  have h := Real.log_le_sub_one_of_pos (div_pos ha hn)
  rw [Real.log_div ha.ne' hn.ne'] at h
  have h' := mul_le_mul_of_nonneg_left h (show 0 ≤ (n : ℝ) / 2 by positivity)
  have he : ((n : ℝ) / 2) * (((n : ℝ) + p) / n - 1) = p / 2 := by
    field_simp
    <;> ring
  rw [he] at h'
  nlinarith

lemma upper_moment {p : ℝ} (hp : 2 ≤ p) :
    (∫ u : E, ‖u‖ ^ p ∂stdGaussian E) ≤ (p + Module.finrank ℝ E) ^ (p / 2) := by
  by_cases hn0 : Module.finrank ℝ E = 0
  · haveI : Subsingleton E := Module.finrank_zero_iff.mp hn0
    have hz (u : E) : u = 0 := Subsingleton.elim _ _
    simp only [hz, norm_zero, Real.zero_rpow (show p ≠ 0 by linarith), integral_zero]
    positivity
  have hn : 0 < (Module.finrank ℝ E : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hp0 : 0 < p := by linarith
  let a : ℝ := Module.finrank ℝ E + p
  let t : ℝ := p / (2 * a)
  have ha : 0 < a := by dsimp [a]; positivity
  have ht : t < 1 / 2 := by
    dsimp [t]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * a)).mpr
    dsimp [a]
    linarith
  have hi := integral_mono (moment_integrable (E := E) hp0.le)
    ((exp_integrable (E := E) ht).const_mul (a ^ (p / 2) * Real.exp (-p / 2)))
    (fun u => pointwise_bound (norm_nonneg u) ha hp0)
  rw [integral_const_mul, exp_integral ht] at hi
  have hm := mgf_bound (Module.finrank ℝ E) hn hp0
  have hk : (a ^ (p / 2) * Real.exp (-p / 2)) * Real.exp (p / 2) = a ^ (p / 2) := by
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
    simp
  calc
    (∫ u : E, ‖u‖ ^ p ∂stdGaussian E)
        ≤ (a ^ (p / 2) * Real.exp (-p / 2)) * (Real.sqrt (1 - 2 * t))⁻¹ ^ Module.finrank ℝ E := hi
    _ ≤ (a ^ (p / 2) * Real.exp (-p / 2)) * Real.exp (p / 2) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = a ^ (p / 2) := hk
    _ = (p + Module.finrank ℝ E) ^ (p / 2) := by dsimp [a]; congr 1; ring

end AGaussianMoment

theorem solution (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (p : ℝ) :
    (0 ≤ p → p ≤ 2 → RandomGradFree.Shared.moment E p ≤ (Module.finrank ℝ E : ℝ) ^ (p / 2)) ∧
    (2 ≤ p → (Module.finrank ℝ E : ℝ) ^ (p / 2) ≤ RandomGradFree.Shared.moment E p ∧
      RandomGradFree.Shared.moment E p ≤ (p + Module.finrank ℝ E) ^ (p / 2))  := by
  constructor
  · intro hp hp2
    exact AGaussianMoment.low_moment hp hp2
  · intro hp
    exact ⟨AGaussianMoment.lower_moment hp, AGaussianMoment.upper_moment hp⟩
