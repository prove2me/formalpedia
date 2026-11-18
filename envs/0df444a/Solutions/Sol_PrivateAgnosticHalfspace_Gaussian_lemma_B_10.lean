-- Prove2me | solution 1 for PrivateAgnosticHalfspace.Gaussian.lemma_B_10
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:07:01.785207+00:00
-- url     : https://prove2.me/submissions/b4d136c6-a94f-4091-ba79-e79b3e653f4a

import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_8
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod

section
-- Solutions.UnivariateGaussianBasis
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma gaussian_coordinate_map (d : ℕ) (i : Fin d) :
    (gaussian d).map (fun x : Vec d => x i) = gaussianReal 0 1 := by
  rw [gaussian, ← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  change (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map (Function.eval i) = _
  exact (measurePreserving_eval (μ := fun _ : Fin d => gaussianReal 0 1) i).map_eq
lemma gaussian_coordinate_preserving (d : ℕ) (i : Fin d) :
    MeasurePreserving (fun x : Vec d => x i) (gaussian d) (gaussianReal 0 1) :=
  ⟨by fun_prop, gaussian_coordinate_map d i⟩
noncomputable def reindexHilbertBasis {ι κ E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (b : HilbertBasis ι ℝ E) (e : κ ≃ ι) : HilbertBasis κ ℝ E :=
  HilbertBasis.mk (b.orthonormal.comp e e.injective) (by
    have hr : Set.range (fun j => b (e j)) = Set.range b := by
      exact e.surjective.range_comp b
    change ⊤ ≤ (Submodule.span ℝ (Set.range (fun j => b (e j)))).topologicalClosure
    rw [hr, b.dense_span])
lemma reindexHilbertBasis_apply {ι κ E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (b : HilbertBasis ι ℝ E) (e : κ ≃ ι) (j : κ) :
    reindexHilbertBasis b e j = b (e j) := by
  simp only [reindexHilbertBasis, HilbertBasis.coe_mk, Function.comp_apply]
lemma univariate_gaussian_basis :
    ∃ b : HilbertBasis ℕ ℝ (Lp ℝ 2 (gaussian 1)),
      ∀ n, (fun x => (b n) x) =ᵐ[gaussian 1]
        (fun x => AMPLowDeg.RankOne.hermNorm n (x 0)) := by
  obtain ⟨b, hb⟩ := (lemma_B_8 1).2.2.1
  let e : ℕ ≃ (Fin 1 → ℕ) := (Equiv.funUnique (Fin 1) ℕ).symm
  refine ⟨reindexHilbertBasis b e, ?_⟩
  intro n
  rw [reindexHilbertBasis_apply]
  convert! hb (e n) using 1
  ext x
  simp [hermite, e, Equiv.funUnique]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.GaussianStein
open MeasureTheory ProbabilityTheory BookProof.HermiteCore
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma integrable_bounded_poly_gauss (g : ℝ → ℝ) (hg : Measurable g) (B : ℝ)
    (hB : ∀ x, |g x| ≤ B) (Q : Polynomial ℝ) :
    Integrable (fun x => g x * Q.eval x * gaussW x) volume := by
  have hm : Measurable (fun x => g x * Q.eval x * gaussW x) :=
    (hg.mul Q.continuous.measurable).mul (by unfold gaussW; fun_prop)
  apply ((integrable_poly_mul_gaussW Q).norm.const_mul B).mono' hm.aestronglyMeasurable
  exact ae_of_all volume (fun x => by
    simp only [Real.norm_eq_abs,abs_mul]
    calc
      _ = |g x| * |Q.eval x * gaussW x| := by rw [abs_mul]; ring
      _ ≤ B * |Q.eval x * gaussW x| := mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)
      _ = _ := by rw [abs_mul])

lemma weighted_stein_hermite (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (B0 B1 : ℝ)
    (hB0 : ∀ x, |g x| ≤ B0) (hB1 : ∀ x, |deriv g x| ≤ B1) (n : ℕ) :
    (∫ x, g x * (hermiteR (n+1)).eval x * gaussW x) =
      ∫ x, deriv g x * (hermiteR n).eval x * gaussW x := by
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hgc : Continuous (deriv g) := hg.continuous_deriv (by simp)
  have hv (x : ℝ) : HasDerivAt (fun x => (hermiteR n).eval x * gaussW x)
      (-((hermiteR (n+1)).eval x * gaussW x)) x := by
    convert! ((hermiteR n).hasDerivAt x).mul (hasDerivAt_gaussW x) using 1
    rw [hermiteR_succ]
    simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_X]
    ring
  have hi0 := integrable_bounded_poly_gauss g hg.continuous.measurable B0 hB0 (hermiteR n)
  have hi1 := integrable_bounded_poly_gauss g hg.continuous.measurable B0 hB0 (hermiteR (n+1))
  have hi2 := integrable_bounded_poly_gauss (deriv g) hgc.measurable B1 hB1 (hermiteR n)
  have hleft : Integrable (g * (fun x => -((hermiteR (n+1)).eval x * gaussW x))) volume := by
    convert! hi1.neg using 1
    funext x; simp only [Pi.mul_apply,Pi.neg_apply]; ring
  have hright : Integrable ((deriv g) * (fun x => (hermiteR n).eval x * gaussW x)) volume := by
    convert! hi2 using 1
    funext x; simp only [Pi.mul_apply]; ring
  have hprod : Integrable (g * (fun x => (hermiteR n).eval x * gaussW x)) volume := by
    convert! hi0 using 1
    funext x; simp only [Pi.mul_apply]; ring
  have hh := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => (hgd x).hasDerivAt)
    (fun x _ => hv x) hleft hright hprod
  have he : (∫ x, g x * -((hermiteR (n+1)).eval x * gaussW x)) =
      -(∫ x, g x * (hermiteR (n+1)).eval x * gaussW x) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact ae_of_all volume (fun x => by ring)
  rw [he] at hh
  have hr : (∫ x, deriv g x * ((hermiteR n).eval x * gaussW x)) =
      (∫ x, deriv g x * (hermiteR n).eval x * gaussW x) := by
    apply integral_congr_ae
    exact ae_of_all volume (fun x => by ring)
  rw [hr] at hh
  linarith
lemma weighted_stein_iterated (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (B : ℕ → ℝ) (hB : ∀ n x, |iteratedDeriv n g x| ≤ B n) (n : ℕ) :
    (∫ x, g x * (hermiteR n).eval x * gaussW x) =
      ∫ x, iteratedDeriv n g x * gaussW x := by
  induction n generalizing g B with
  | zero => simp [hermiteR]
  | succ n ih =>
    rw [weighted_stein_hermite g hg (B 0) (B 1) (by simpa using hB 0)
      (by simpa [iteratedDeriv_succ] using hB 1) n]
    have hgd : ContDiff ℝ (⊤ : ℕ∞) (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
    rw [ih (deriv g) hgd (fun k => B (k+1)) (by
      intro k x
      simpa [iteratedDeriv_succ'] using hB (k+1) x)]
    simp only [iteratedDeriv_succ']
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.GaussianHermiteCoefficient
open MeasureTheory ProbabilityTheory BookProof.HermiteCore
open scoped NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma gaussian_stein_normalized (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (B : ℕ → ℝ) (hB : ∀ n x, |iteratedDeriv n g x| ≤ B n) (n : ℕ) :
    (∫ x, g x * AMPLowDeg.RankOne.hermNorm n x ∂gaussianReal 0 1) =
      (∫ x, iteratedDeriv n g x ∂gaussianReal 0 1) / Real.sqrt (n.factorial : ℝ) := by
  have hpdf (x : ℝ) : gaussianPDFReal 0 1 x =
      (Real.sqrt (2*Real.pi))⁻¹ * gaussW x := by
    simp [gaussianPDFReal, gaussW]
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul, hpdf]
  have he (x : ℝ) : (Real.sqrt (2*Real.pi))⁻¹ * gaussW x *
      (g x * AMPLowDeg.RankOne.hermNorm n x) =
      (Real.sqrt (2*Real.pi))⁻¹ *
      (g x * (hermiteR n).eval x * gaussW x) / Real.sqrt (n.factorial : ℝ) := by
    unfold AMPLowDeg.RankOne.hermNorm hermiteR
    ring
  simp_rw [he]
  rw [integral_div, integral_const_mul, weighted_stein_iterated g hg B hB n]
  have her (x : ℝ) : (Real.sqrt (2*Real.pi))⁻¹ * gaussW x * iteratedDeriv n g x =
      (Real.sqrt (2*Real.pi))⁻¹ * (iteratedDeriv n g x * gaussW x) := by ring
  simp_rw [her]
  rw [integral_const_mul]
lemma gaussian_hermite_coefficient_bound (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (B : ℝ) (hB : ∀ n x, |iteratedDeriv n g x| ≤ B^n) (n : ℕ) :
    |∫ x, g x * AMPLowDeg.RankOne.hermNorm n x ∂gaussianReal 0 1| ≤
      B^n / Real.sqrt (n.factorial : ℝ) := by
  rw [gaussian_stein_normalized g hg (fun n => B^n) hB n, abs_div,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const
    (μ := gaussianReal 0 1) (f := iteratedDeriv n g) (C := B^n)
    (ae_of_all _ (fun x => by
    simpa [Real.norm_eq_abs] using hB n x))
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.HilbertTruncation
open scoped BigOperators
open Filter Finset
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def hilbertTruncation (b : HilbertBasis ℕ ℝ E) (u : E) (p : ℕ) : E :=
  ∑ j ∈ range (p+1), (inner ℝ (b j) u) • b j
lemma hilbertTruncation_coeff (b : HilbertBasis ℕ ℝ E) (u : E) (p n : ℕ) :
    inner ℝ (b n) (hilbertTruncation b u p) =
      if n ≤ p then inner ℝ (b n) u else 0 := by
  classical
  simp only [hilbertTruncation, inner_sum, inner_smul_right,
    orthonormal_iff_ite.mp b.orthonormal]
  simp [mul_ite, Nat.lt_succ_iff, eq_comm]
lemma hilbertTruncation_norm_sq (b : HilbertBasis ℕ ℝ E) (u : E) (p : ℕ) :
    ‖hilbertTruncation b u p‖^2 = ∑ j ∈ range (p+1), (inner ℝ (b j) u)^2 := by
  rw [← real_inner_self_eq_norm_sq, hilbertTruncation]
  rw [sum_inner]
  apply sum_congr rfl
  intro j hj
  simp only [inner_smul_left, conj_trivial]
  rw [← hilbertTruncation, hilbertTruncation_coeff,
    if_pos (Nat.lt_succ_iff.mp (mem_range.mp hj)), pow_two]
lemma hilbertTruncation_norm_le (b : HilbertBasis ℕ ℝ E) (u : E) (p : ℕ) :
    ‖hilbertTruncation b u p‖ ≤ ‖u‖ := by
  have h := b.orthonormal.sum_inner_products_le u (s := range (p+1))
  simp only [Real.norm_eq_abs, sq_abs] at h
  rw [← hilbertTruncation_norm_sq] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
lemma hilbertTruncation_tail_sq (b : HilbertBasis ℕ ℝ E) (u : E) (p : ℕ) :
    ‖u - hilbertTruncation b u p‖^2 =
      ∑' n : ℕ, if p < n then (inner ℝ (b n) u)^2 else 0 := by
  have h := b.tsum_inner_mul_inner (u-hilbertTruncation b u p) (u-hilbertTruncation b u p)
  rw [real_inner_self_eq_norm_sq] at h
  rw [← h]
  apply tsum_congr
  intro n
  rw [real_inner_comm (b n) (u-hilbertTruncation b u p), inner_sub_right,
    hilbertTruncation_coeff]
  by_cases hn : n ≤ p <;> simp [hn, Nat.lt_of_not_ge, Nat.not_lt.mpr, pow_two, real_inner_comm]
lemma exponential_factorial_tail (H : ℝ) (hH : 1 ≤ H) (p : ℕ)
    (hp : (Real.exp 1 + 2) * H^2 ≤ (p : ℝ)) :
    (∑' n : ℕ, if p < n then H^(2*n)/(n.factorial : ℝ) else 0) ≤ H⁻¹^2 := by
  let a : ℕ → ℝ := fun n => Real.exp (-(p : ℝ)) * (Real.exp 1 * H^2)^n / n.factorial
  have ha : HasSum a (Real.exp (-(p : ℝ)) * Real.exp (Real.exp 1 * H^2)) := by
    have he : HasSum (fun n : ℕ => (Real.exp 1 * H^2)^n / n.factorial)
        (Real.exp (Real.exp 1 * H^2)) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp _
    convert! he.mul_left (Real.exp (-(p : ℝ))) using 1
    funext n; simp [a]; ring
  have hb (n : ℕ) : (if p < n then H^(2*n)/(n.factorial : ℝ) else 0) ≤ a n := by
    by_cases hn : p < n
    · rw [if_pos hn]
      have hpn : (p : ℝ) ≤ n := by exact_mod_cast hn.le
      have he : 1 ≤ Real.exp (n-p : ℝ) := Real.one_le_exp_iff.mpr (by linarith)
      have heq : a n = Real.exp (n-p : ℝ) * H^(2*n) / n.factorial := by
        dsimp [a]
        rw [mul_pow, ← Real.exp_nat_mul, ← mul_assoc, ← Real.exp_add]
        congr 2
        · congr 1; ring
        · rw [pow_mul]
      rw [heq]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact le_mul_of_one_le_left (by positivity) he
    · simp only [if_neg hn]
      dsimp [a]; positivity
  calc
    _ ≤ ∑' n, a n := (Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) hb ha.summable).tsum_le_tsum hb ha.summable
    _ = Real.exp (-(p : ℝ)) * Real.exp (Real.exp 1 * H^2) := ha.tsum_eq
    _ ≤ Real.exp (-2*H^2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    _ ≤ H⁻¹^2 := by
      have hh : 0 < H := by linarith
      have he : H^2 ≤ Real.exp (2*H^2) := by
        linarith [Real.add_one_le_exp (2*H^2), sq_nonneg H]
      rw [show -2*H^2 = -(2*H^2) by ring, Real.exp_neg, inv_pow, ← inv_pow]
      simpa only [inv_pow] using (inv_le_inv₀ (by positivity) (by positivity)).mpr he
lemma hilbertTruncation_error_le (b : HilbertBasis ℕ ℝ E) (u : E)
    (H : ℝ) (hH : 1 ≤ H)
    (hc : ∀ n, |inner ℝ (b n) u| ≤ H^n / Real.sqrt (n.factorial : ℝ))
    (p : ℕ) (hp : (Real.exp 1 + 2)*H^2 ≤ (p : ℝ)) :
    ‖u-hilbertTruncation b u p‖ ≤ H⁻¹ := by
  have hs : HasSum (fun n : ℕ => (H^2)^n/(n.factorial : ℝ)) (Real.exp (H^2)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have hst : Summable (fun n : ℕ => if p < n then H^(2*n)/(n.factorial : ℝ) else 0) := by
    apply Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) _ hs.summable
    intro n
    split_ifs
    · rw [pow_mul]
    · positivity
  have hcoeff (n : ℕ) : (inner ℝ (b n) u)^2 ≤ H^(2*n)/(n.factorial : ℝ) := by
    have hn : 0 ≤ H^n / Real.sqrt (n.factorial : ℝ) := by positivity
    have hh := (sq_le_sq₀ (abs_nonneg _) hn).mpr (hc n)
    rw [sq_abs, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at hh
    convert! hh using 1
    rw [← pow_mul, Nat.mul_comm n 2]
  have htail (n : ℕ) : (if p < n then (inner ℝ (b n) u)^2 else 0) ≤
      if p < n then H^(2*n)/(n.factorial : ℝ) else 0 := by
    split_ifs <;> simp_all [hcoeff]
  have hsc : Summable (fun n : ℕ => if p < n then (inner ℝ (b n) u)^2 else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) htail hst
  have he : ‖u-hilbertTruncation b u p‖^2 ≤ H⁻¹^2 := by
    rw [hilbertTruncation_tail_sq]
    exact (hsc.tsum_le_tsum htail hst).trans (exponential_factorial_tail H hH p hp)
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp he
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.L2Integral
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma norm_toLp_two_sq {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) (f : Z → ℝ)
    (hf : MemLp f 2 μ) : ‖hf.toLp f‖^2 = ∫ z, f z^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with z hz
  rw [hz]
  change f z * f z = f z^2
  ring
lemma integral_abs_le_norm_toLp {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (f : Z → ℝ) (hf : MemLp f 2 μ) :
    (∫ z, |f z| ∂μ) ≤ ‖hf.toLp f‖ := by
  have hi := (hf.integrable (by norm_num)).norm
  have hsq : Integrable ((fun x : ℝ => x^2) ∘ (fun z => |f z|)) μ := by
    simpa [Function.comp_def, sq_abs] using hf.integrable_sq
  have h := (convexOn_pow (𝕜 := ℝ) 2).map_integral_le (continuous_pow 2).continuousOn
    isClosed_Ici (ae_of_all μ (fun z => abs_nonneg (f z))) (by
      simpa [Real.norm_eq_abs] using hi) hsq
  simp only [Function.comp_def, sq_abs] at h
  rw [← norm_toLp_two_sq μ f hf] at h
  exact (sq_le_sq₀ (integral_nonneg (fun z => abs_nonneg _)) (norm_nonneg _)).mp h
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.UnivariateApproximation
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def hermitePartial (a : ℕ → ℝ) (p : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (p+1), a j * AMPLowDeg.RankOne.hermNorm j x
lemma hermitePartial_continuous (a : ℕ → ℝ) (p : ℕ) : Continuous (hermitePartial a p) := by
  unfold hermitePartial AMPLowDeg.RankOne.hermNorm
  fun_prop
lemma truncation_coe_partial (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (gaussian 1)))
    (hb : ∀ n, (fun x => (b n) x) =ᵐ[gaussian 1]
      (fun x => AMPLowDeg.RankOne.hermNorm n (x 0)))
    (u : Lp ℝ 2 (gaussian 1)) (p : ℕ) :
    (fun x : Vec 1 => hilbertTruncation b u p x) =ᵐ[gaussian 1]
      (fun x => hermitePartial (fun n => inner ℝ (b n) u) p (x 0)) := by
  have hs := Lp.coeFn_fun_finsetSum (range (p+1)) (fun n => (inner ℝ (b n) u) • b n)
  filter_upwards [hs, ae_all_iff.mpr (fun n => Lp.coeFn_smul (inner ℝ (b n) u) (b n)),
    ae_all_iff.mpr hb] with x hx hsm hbs
  change (∑ j ∈ range (p+1), inner ℝ (b j) u • b j) x = _
  rw [hx]
  unfold hermitePartial
  apply sum_congr rfl
  intro j hj
  rw [hsm j]
  change inner ℝ (b j) u * (b j) x = _
  rw [hbs j]
lemma hermite_projection_approximation (g : ℝ → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg1 : ∀ x, |g x| ≤ 1)
    (H : ℝ) (hH : 1 ≤ H) (hd : ∀ n x, |iteratedDeriv n g x| ≤ H^n)
    (p : ℕ) (hp : (Real.exp 1 + 2)*H^2 ≤ (p : ℝ)) :
    ∃ a : ℕ → ℝ,
      (∑ j ∈ range (p+1), (a j)^2) ≤ 1 ∧
      Integrable (fun x => |g x - hermitePartial a p x|) (gaussianReal 0 1) ∧
      (∫ x, |g x - hermitePartial a p x| ∂gaussianReal 0 1) ≤ H⁻¹ := by
  let μ := gaussian 1
  letI : IsProbabilityMeasure μ := by dsimp [μ, gaussian]; infer_instance
  have hgm : MemLp g 2 (gaussianReal 0 1) :=
    MemLp.of_bound hg.continuous.aestronglyMeasurable 1
      (ae_of_all _ (fun x => by simpa [Real.norm_eq_abs] using hg1 x))
  have hgl := hgm.comp_measurePreserving (gaussian_coordinate_preserving 1 0)
  let u : Lp ℝ 2 μ := hgl.toLp _
  obtain ⟨b,hb⟩ := univariate_gaussian_basis
  let a : ℕ → ℝ := fun n => inner ℝ (b n) u
  have hcoef (n : ℕ) : a n = ∫ x, g x * AMPLowDeg.RankOne.hermNorm n x ∂gaussianReal 0 1 := by
    dsimp [a]
    rw [L2.inner_def]
    calc
      _ = ∫ x : Vec 1, g (x 0) * AMPLowDeg.RankOne.hermNorm n (x 0) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hb n, hgl.coeFn_toLp] with x hx hu
        rw [hx, hu]
        simp [Function.comp_def, RCLike.inner_apply, mul_comm]
      _ = _ := by
        rw [← gaussian_coordinate_map 1 0, integral_map (by fun_prop)
          (by
            have hh : Continuous (fun x => g x * AMPLowDeg.RankOne.hermNorm n x) := by
              apply hg.continuous.mul
              unfold AMPLowDeg.RankOne.hermNorm; fun_prop
            exact hh.aestronglyMeasurable)]
  have hcb (n : ℕ) : |a n| ≤ H^n / Real.sqrt (n.factorial : ℝ) := by
    rw [hcoef]
    exact gaussian_hermite_coefficient_bound g hg H hd n
  let v := hilbertTruncation b u p
  have hv : (v : Vec 1 → ℝ) =ᵐ[μ] (fun x => hermitePartial a p (x 0)) :=
    truncation_coe_partial b hb u p
  have hrv : ((u-v : Lp ℝ 2 μ) : Vec 1 → ℝ) =ᵐ[μ]
      (fun x => g (x 0) - hermitePartial a p (x 0)) := by
    filter_upwards [Lp.coeFn_sub u v, hgl.coeFn_toLp, hv] with x hx hu hvx
    rw [hx]
    change u x - v x = _
    rw [hu, hvx]
    rfl
  have hrmem : MemLp (fun x : Vec 1 => g (x 0) - hermitePartial a p (x 0)) 2 μ :=
    (Lp.memLp (u-v)).ae_eq hrv
  have hu1 : ‖u‖^2 ≤ 1 := by
    rw [norm_toLp_two_sq μ _ hgl]
    calc
      _ ≤ ∫ _ : Vec 1, (1 : ℝ) ∂μ := by
        apply integral_mono hgl.integrable_sq (integrable_const 1)
        intro x
        exact (sq_le_one_iff_abs_le_one _).mpr (hg1 (x 0))
      _ = _ := by simp
  refine ⟨a, ?_, ?_, ?_⟩
  · rw [← hilbertTruncation_norm_sq]
    exact (pow_le_pow_left₀ (norm_nonneg _) (hilbertTruncation_norm_le b u p) 2).trans hu1
  · have hi := (hrmem.integrable (by norm_num)).norm
    have hpres := gaussian_coordinate_preserving 1 0
    apply (hpres.integrable_comp (by
      exact ((hg.continuous.sub (hermitePartial_continuous a p)).abs.measurable).aestronglyMeasurable)).mp
    simpa only [Real.norm_eq_abs, Function.comp_def] using hi
  · have hi := integral_abs_le_norm_toLp μ _ hrmem
    have hto : hrmem.toLp _ = u-v := by
      apply Lp.ext
      exact hrmem.coeFn_toLp.trans hrv.symm
    rw [hto] at hi
    have hpres := gaussian_coordinate_preserving 1 0
    have he : (∫ x : Vec 1, |g (x 0) - hermitePartial a p (x 0)| ∂μ) =
        ∫ x, |g x-hermitePartial a p x| ∂gaussianReal 0 1 := by
      rw [← gaussian_coordinate_map 1 0, integral_map (by fun_prop) (by
        exact (hg.continuous.sub (hermitePartial_continuous a p)).abs.measurable.aestronglyMeasurable)]
    rw [he] at hi
    exact hi.trans (hilbertTruncation_error_le b u H hH hcb p hp)
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.HermitePartialNorm
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma orthonormal_finite_sum_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} (b : ι → E) (hb : Orthonormal ℝ b) (s : Finset ι) (a : ι → ℝ) :
    ‖∑ j ∈ s, a j • b j‖^2 = ∑ j ∈ s, (a j)^2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sum, sum_inner, inner_smul_left, inner_smul_right,
    conj_trivial, orthonormal_iff_ite.mp hb]
  simp [mul_ite, ite_mul, pow_two]
lemma finitePartial_coe (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (gaussian 1)))
    (hb : ∀ n, (fun x => (b n) x) =ᵐ[gaussian 1]
      (fun x => AMPLowDeg.RankOne.hermNorm n (x 0)))
    (a : ℕ → ℝ) (p : ℕ) :
    (fun x : Vec 1 => (∑ j ∈ range (p+1), a j • b j) x) =ᵐ[gaussian 1]
      (fun x => hermitePartial a p (x 0)) := by
  have hs := Lp.coeFn_fun_finsetSum (range (p+1)) (fun n => a n • b n)
  filter_upwards [hs, ae_all_iff.mpr (fun n => Lp.coeFn_smul (a n) (b n)),
    ae_all_iff.mpr hb] with x hx hsm hbs
  rw [hx]
  unfold hermitePartial
  apply sum_congr rfl
  intro j hj
  rw [hsm j]
  change a j * (b j) x = _
  rw [hbs j]
lemma hermitePartial_memLp (a : ℕ → ℝ) (p : ℕ) :
    MemLp (hermitePartial a p) 2 (gaussianReal 0 1) := by
  obtain ⟨b,hb⟩ := univariate_gaussian_basis
  have hv := finitePartial_coe b hb a p
  have hm := (Lp.memLp (∑ j ∈ range (p+1), a j • b j)).ae_eq hv
  rw [← gaussian_coordinate_map 1 0]
  exact (memLp_map_measure_iff (hermitePartial_continuous a p).aestronglyMeasurable
    (by fun_prop)).mpr hm
lemma hermitePartial_square_integral (a : ℕ → ℝ) (p : ℕ) :
    (∫ x, (hermitePartial a p x)^2 ∂gaussianReal 0 1) = ∑ j ∈ range (p+1), (a j)^2 := by
  obtain ⟨b,hb⟩ := univariate_gaussian_basis
  let v := ∑ j ∈ range (p+1), a j • b j
  have hv := finitePartial_coe b hb a p
  have hmem : MemLp (fun x : Vec 1 => hermitePartial a p (x 0)) 2 (gaussian 1) :=
    (Lp.memLp v).ae_eq hv
  have he : hmem.toLp _ = v := by
    apply Lp.ext
    exact hmem.coeFn_toLp.trans hv.symm
  rw [← gaussian_coordinate_map 1 0, integral_map (by fun_prop) (by
    exact ((hermitePartial_continuous a p).pow 2).aestronglyMeasurable)]
  rw [← norm_toLp_two_sq (gaussian 1) _ hmem, he]
  exact orthonormal_finite_sum_norm_sq b b.orthonormal _ a
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.BandlimitedKernel
open MeasureTheory FourierTransform Real
open scoped SchwartzMap FourierTransform BigOperators
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma compact_fourier_derivative_bound (b : 𝓢(ℝ, ℂ)) (R : ℝ) (hR : 0 ≤ R)
    (hb : ∀ x, R < |x| → b x = 0) (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n (𝓕 (b : ℝ → ℂ)) x‖ ≤
      (2 * Real.pi * R)^n * ∫ y : ℝ, ‖b y‖ := by
  have himom (k : ℕ) : Integrable (fun y : ℝ => y^k • b y) := by
    apply (b.integrable_pow_mul volume k).mono' (by fun_prop)
    exact ae_of_all volume (fun y => by simp [norm_smul])
  rw [Real.iteratedDeriv_fourier (N := ⊤) (fun k _ => himom k) (by simp),
    Real.fourier_eq]
  calc
    _ ≤ ∫ y : ℝ, ‖(-2 * Real.pi * Complex.I * (y : ℂ))^n • b y‖ := by
      simpa [mul_comm] using norm_integral_le_integral_norm
        (fun y : ℝ => 𝐞 (- y * x) • ((-2 * Real.pi * Complex.I * (y : ℂ))^n • b y)) (μ := volume)
    _ ≤ ∫ y : ℝ, (2 * Real.pi * R)^n * ‖b y‖ := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun y => norm_nonneg _))
        (b.integrable.norm.const_mul _) (ae_of_all _ (fun y => ?_))
      by_cases hy : R < |y|
      · simp [hb y hy]
      · simp only [norm_smul, norm_pow, norm_mul, norm_neg, Complex.norm_ofNat,
          Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one, abs_of_pos Real.pi_pos]
        gcongr
        exact le_of_not_gt hy
    _ = _ := integral_const_mul _ _

lemma square_fourier_derivative_bound (b : 𝓢(ℝ, ℂ)) (R : ℝ) (hR : 0 ≤ R)
    (hb : ∀ x, R < |x| → b x = 0) (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (fun y => ‖𝓕 (b : ℝ → ℂ) y‖^2) x| ≤
      (4 * Real.pi * R)^n * (∫ y : ℝ, ‖b y‖)^2 := by
  let f : 𝓢(ℝ, ℂ) := 𝓕 b
  have hf : (f : ℝ → ℂ) = 𝓕 (b : ℝ → ℂ) := SchwartzMap.fourier_coe b
  have hs : ContDiff ℝ (⊤ : ℕ∞) (f : ℝ → ℂ) := f.smooth ⊤
  have hi : 0 ≤ ∫ y : ℝ, ‖b y‖ := integral_nonneg (fun y => norm_nonneg _)
  have hd (j : ℕ) : ‖iteratedDeriv j (f : ℝ → ℂ) x‖ ≤
      (2 * Real.pi * R)^j * ∫ y : ℝ, ‖b y‖ := by
    rw [hf]; exact compact_fourier_derivative_bound b R hR hb j x
  have h := (innerSL ℝ (E := ℂ)).norm_iteratedFDeriv_le_of_bilinear
    hs hs x (n := n) (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hefun : (fun y => (innerSL ℝ (E := ℂ)) (f y) (f y)) =
      (fun y => ‖f y‖^2) := by
    funext y
    change inner ℝ (f y) (f y) = _
    exact real_inner_self_eq_norm_sq _
  rw [hefun] at h
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
  rw [← hf]
  calc
    _ ≤ ‖innerSL ℝ (E := ℂ)‖ * ∑ j ∈ Finset.range (n+1),
      (n.choose j : ℝ) * ‖iteratedDeriv j (f : ℝ → ℂ) x‖ *
        ‖iteratedDeriv (n-j) (f : ℝ → ℂ) x‖ := by simpa [Real.norm_eq_abs] using h
    _ ≤ ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
        ((2 * Real.pi * R)^j * ∫ y : ℝ, ‖b y‖) *
        ((2 * Real.pi * R)^(n-j) * ∫ y : ℝ, ‖b y‖) := by
      apply (mul_le_of_le_one_left (by positivity) (norm_innerSL_le ℝ)).trans
      apply Finset.sum_le_sum
      intro j hj
      gcongr
      · exact hd j
      · exact hd (n-j)
    _ = (4 * Real.pi * R)^n * (∫ y : ℝ, ‖b y‖)^2 := by
      have he (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
          (n.choose j : ℝ) * ((2 * Real.pi * R)^j * ∫ y : ℝ, ‖b y‖) *
          ((2 * Real.pi * R)^(n-j) * ∫ y : ℝ, ‖b y‖) =
          (n.choose j : ℝ) * (2 * Real.pi * R)^n * (∫ y : ℝ, ‖b y‖)^2 := by
        have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
        have hp : (2 * Real.pi * R)^j * (2 * Real.pi * R)^(n-j) =
            (2 * Real.pi * R)^n := by
          rw [← pow_add, Nat.add_sub_of_le hjn]
        calc
          _ = (n.choose j : ℝ) * ((2 * Real.pi * R)^j *
            (2 * Real.pi * R)^(n-j)) * (∫ y : ℝ, ‖b y‖)^2 := by ring
          _ = _ := by rw [hp]
      rw [Finset.sum_congr rfl he, ← Finset.sum_mul, ← Finset.sum_mul]
      have hc : ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) = 2^n := by
        exact_mod_cast Nat.sum_range_choose n
      rw [hc, ← mul_pow]
      congr 2 <;> ring
end PrivateAgnosticHalfspace.Gaussian

namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def squareFourier (b : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℝ) :=
  SchwartzMap.pairing (innerSL ℝ) (𝓕 b) (𝓕 b)
lemma squareFourier_apply (b : 𝓢(ℝ, ℂ)) (x : ℝ) :
    squareFourier b x = ‖𝓕 (b : ℝ → ℂ) x‖^2 := by
  change inner ℝ (𝓕 b x) (𝓕 b x) = _
  rw [real_inner_self_eq_norm_sq, SchwartzMap.fourier_coe]

lemma exists_bandlimited_probability_kernel :
    ∃ (K : 𝓢(ℝ, ℝ)) (A B : ℝ),
      0 < A ∧ 0 < B ∧ (∀ x, 0 ≤ K x) ∧ (∫ x, K x) = 1 ∧
      ∀ n x, |iteratedDeriv n (K : ℝ → ℝ) x| ≤ A * B^n := by
  let χ : ContDiffBump (0 : ℝ) := default
  let b : 𝓢(ℝ, ℂ) := (χ.hasCompactSupport.comp_left (show Complex.ofRealCLM 0 = 0 from rfl)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp χ.contDiff)
  have hb (x : ℝ) : b x = (χ x : ℂ) := rfl
  have hb0 : b 0 = 1 := by rw [hb, χ.one_of_mem_closedBall (by simp [χ.rIn_pos.le])]; simp
  have hsupport : ∀ x, χ.rOut < |x| → b x = 0 := by
    intro x hx
    rw [hb, χ.zero_of_le_dist (by simpa [Real.dist_eq] using hx.le)]
    simp
  let I : ℝ := ∫ x, ‖b x‖^2
  have hIs : Integrable (fun x => ‖b x‖^2) := by
    let q := SchwartzMap.pairing (innerSL ℝ) b b
    convert! (q.integrable (μ := volume)) using 1
    funext x
    exact (real_inner_self_eq_norm_sq (b x)).symm
  have hI : 0 < I := by
    apply integral_pos_of_integrable_nonneg_nonzero (by fun_prop) hIs (fun x => sq_nonneg _)
      (x := 0)
    simp [hb0]
  let K : 𝓢(ℝ, ℝ) := I⁻¹ • squareFourier b
  have hK (x : ℝ) : K x = I⁻¹ * ‖𝓕 (b : ℝ → ℂ) x‖^2 := by
    simp [K, squareFourier_apply]
  have hA : 0 < 1 + I⁻¹ * (∫ x : ℝ, ‖b x‖)^2 := by positivity
  refine ⟨K, 1 + I⁻¹ * (∫ x : ℝ, ‖b x‖)^2, 4 * Real.pi * χ.rOut,
    hA, mul_pos (by positivity) χ.rOut_pos, (fun x => by rw [hK]; positivity), ?_, ?_⟩
  · simp_rw [hK]
    rw [integral_const_mul, ← SchwartzMap.fourier_coe b, SchwartzMap.integral_norm_sq_fourier]
    exact inv_mul_cancel₀ hI.ne'
  · intro n x
    have hfun : (K : ℝ → ℝ) = fun y => I⁻¹ * ‖𝓕 (b : ℝ → ℂ) y‖^2 := funext hK
    rw [hfun, iteratedDeriv_const_mul_field, abs_mul, abs_of_pos (inv_pos.mpr hI)]
    calc
      _ ≤ I⁻¹ * ((4 * Real.pi * χ.rOut)^n * (∫ y : ℝ, ‖b y‖)^2) :=
        mul_le_mul_of_nonneg_left
          (square_fourier_derivative_bound b χ.rOut χ.rOut_pos.le hsupport n x)
          (inv_nonneg.mpr hI.le)
      _ ≤ _ := by nlinarith [pow_nonneg (show 0 ≤ 4 * Real.pi * χ.rOut from mul_nonneg (by positivity) χ.rOut_pos.le) n]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.SmoothThreshold
open MeasureTheory Set
open scoped SchwartzMap ContDiff
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def kernelCDF (K : ℝ → ℝ) (x : ℝ) : ℝ := ∫ u in Iic x, K u
lemma kernelCDF_hasDerivAt (K : ℝ → ℝ) (hK : Integrable K) (hc : Continuous K) (x : ℝ) :
    HasDerivAt (kernelCDF K) (K x) x := by
  have he (y : ℝ) : kernelCDF K y = kernelCDF K 0 + ∫ u in (0 : ℝ)..y, K u := by
    unfold kernelCDF
    linarith [intervalIntegral.integral_Iic_sub_Iic (hK.integrableOn (s := Iic 0))
      (hK.integrableOn (s := Iic y))]
  rw [show kernelCDF K = (fun y => kernelCDF K 0 + ∫ u in (0 : ℝ)..y, K u) from funext he]
  exact (intervalIntegral.integral_hasDerivAt_right (hK.intervalIntegrable)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add _
lemma kernelCDF_contDiff (K : 𝓢(ℝ, ℝ)) : ContDiff ℝ ∞ (kernelCDF K) := by
  have hd : deriv (kernelCDF K) = K := funext (fun x => (kernelCDF_hasDerivAt K K.integrable K.continuous x).deriv)
  apply contDiff_infty.mpr
  intro n
  cases n with
  | zero => exact contDiff_zero.mpr (show Differentiable ℝ (kernelCDF K) from fun x =>
      (kernelCDF_hasDerivAt K K.integrable K.continuous x).differentiableAt).continuous
  | succ n =>
    rw [show (↑(n+1) : ℕ∞ω) = (n : ℕ∞ω)+1 by simp, contDiff_succ_iff_deriv]
    refine ⟨fun x => (kernelCDF_hasDerivAt K K.integrable K.continuous x).differentiableAt, ?_, ?_⟩
    · simp
    · rw [hd]; exact K.smooth n
lemma kernelCDF_bounds (K : ℝ → ℝ) (hK : Integrable K) (hpos : ∀ x, 0 ≤ K x)
    (hmass : (∫ x, K x) = 1) (x : ℝ) : 0 ≤ kernelCDF K x ∧ kernelCDF K x ≤ 1 := by
  refine ⟨integral_nonneg (fun y => hpos y), ?_⟩
  rw [← hmass]
  exact setIntegral_le_integral hK (ae_of_all _ hpos)
noncomputable def smoothThreshold (K : ℝ → ℝ) (scale θ x : ℝ) : ℝ :=
  2 * kernelCDF K (scale * (x-θ)) - 1
lemma smoothThreshold_abs_le_one (K : ℝ → ℝ) (hK : Integrable K)
    (hpos : ∀ x, 0 ≤ K x) (hmass : (∫ x, K x) = 1) (scale θ x : ℝ) :
    |smoothThreshold K scale θ x| ≤ 1 := by
  have h := kernelCDF_bounds K hK hpos hmass (scale*(x-θ))
  rw [abs_le]
  unfold smoothThreshold
  constructor <;> linarith
lemma smoothThreshold_contDiff (K : 𝓢(ℝ, ℝ)) (scale θ : ℝ) :
    ContDiff ℝ ∞ (smoothThreshold K scale θ) := by
  exact ((contDiff_const.mul ((kernelCDF_contDiff K).comp
    (contDiff_const.mul (contDiff_id.sub contDiff_const)))).sub contDiff_const)
lemma smoothThreshold_deriv (K : 𝓢(ℝ, ℝ)) (scale θ : ℝ) :
    deriv (smoothThreshold K scale θ) = fun x => 2 * scale * K (scale*(x-θ)) := by
  funext x
  have h := (kernelCDF_hasDerivAt K K.integrable K.continuous (scale*(x-θ))).comp x
    (((hasDerivAt_id x).sub_const θ).const_mul scale)
  convert! ((h.const_mul 2).sub_const 1).deriv using 1 <;> ring
lemma smoothThreshold_iteratedDeriv (K : 𝓢(ℝ, ℝ)) (scale θ : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv (n+1) (smoothThreshold K scale θ) x =
      2 * scale^(n+1) * iteratedDeriv n (K : ℝ → ℝ) (scale*(x-θ)) := by
  rw [iteratedDeriv_succ', smoothThreshold_deriv]
  rw [iteratedDeriv_const_mul_field]
  have he : (fun y => K (scale*(y-θ))) = (fun y => (fun z => K (scale*z)) (y-θ)) := rfl
  rw [he, iteratedDeriv_comp_sub_const n (fun z => K (scale*z)) θ,
    iteratedDeriv_comp_const_mul (K.smooth n) scale]
  simp only
  rw [pow_succ]
  ring
lemma smoothThreshold_derivative_bound (K : 𝓢(ℝ, ℝ)) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 < B)
    (hd : ∀ n x, |iteratedDeriv n (K : ℝ → ℝ) x| ≤ A*B^n)
    (scale θ : ℝ) (hscale : 0 ≤ scale) (n : ℕ) (x : ℝ) :
    |iteratedDeriv (n+1) (smoothThreshold K scale θ) x| ≤
      2 * A * scale^(n+1) * B^n := by
  rw [smoothThreshold_iteratedDeriv, abs_mul,
    abs_of_nonneg (mul_nonneg (by norm_num) (pow_nonneg hscale _))]
  calc
    _ ≤ (2 * scale^(n+1)) * (A*B^n) :=
      mul_le_mul_of_nonneg_left (hd n _) (by positivity)
    _ = _ := by ring
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.ThresholdTranslation
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def thresholdStep (θ x : ℝ) : ℝ := if θ ≤ x then 1 else -1
lemma thresholdStep_measurable (θ : ℝ) : Measurable (thresholdStep θ) := by
  unfold thresholdStep
  exact measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const
lemma thresholdStep_abs (θ x : ℝ) : |thresholdStep θ x| = 1 := by
  unfold thresholdStep; split_ifs <;> norm_num
lemma thresholdStep_difference_bound (θ η x : ℝ) :
    |thresholdStep θ x - thresholdStep η x| ≤
      (uIcc θ η).indicator (fun _ => (2 : ℝ)) x := by
  unfold thresholdStep
  by_cases hθ : θ ≤ x <;> by_cases hη : η ≤ x
  · simp only [if_pos hθ, if_pos hη, sub_self, abs_zero]
    exact indicator_nonneg (fun _ _ => by norm_num) x
  · have hx : x ∈ uIcc θ η := by
      simp only [mem_uIcc]
      exact Or.inl ⟨hθ, (lt_of_not_ge hη).le⟩
    norm_num [hθ, hη, hx]
  · have hx : x ∈ uIcc θ η := by
      simp only [mem_uIcc]
      exact Or.inr ⟨hη, (lt_of_not_ge hθ).le⟩
    norm_num [hθ, hη, hx]
  · simp only [if_neg hθ, if_neg hη, sub_self, abs_zero]
    exact indicator_nonneg (fun _ _ => by norm_num) x
lemma gaussianPDF_standard_le (x : ℝ) :
    gaussianPDFReal 0 1 x ≤ (Real.sqrt (2*Real.pi))⁻¹ := by
  unfold gaussianPDFReal
  norm_num only [NNReal.coe_one, mul_one, sub_zero]
  apply mul_le_of_le_one_right (by positivity)
  exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
lemma gaussian_threshold_translation (θ η : ℝ) :
    (∫ x, |thresholdStep θ x - thresholdStep η x| ∂gaussianReal 0 1) ≤
      2 * (Real.sqrt (2*Real.pi))⁻¹ * |θ-η| := by
  have hm : Measurable (fun x => |thresholdStep θ x - thresholdStep η x|) :=
    ((thresholdStep_measurable θ).sub (thresholdStep_measurable η)).abs
  have hb (x : ℝ) : |thresholdStep θ x - thresholdStep η x| ≤ 2 := by
    calc
      _ ≤ |thresholdStep θ x| + |thresholdStep η x| := abs_sub _ _
      _ = _ := by rw [thresholdStep_abs, thresholdStep_abs]; norm_num
  have hi : Integrable (fun x => gaussianPDFReal 0 1 x *
      |thresholdStep θ x - thresholdStep η x|) := by
    apply ((integrable_gaussianPDFReal 0 1).const_mul 2).mono' (by fun_prop)
    exact ae_of_all volume (fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _),
        abs_abs]
      nlinarith [gaussianPDFReal_nonneg 0 1 x, hb x])
  have hj : Integrable ((uIcc θ η).indicator
      (fun _ => 2 * (Real.sqrt (2*Real.pi))⁻¹)) volume := by
    exact integrableOn_const isCompact_uIcc.measure_ne_top |>.integrable_indicator measurableSet_uIcc
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  calc
    _ ≤ ∫ x, (uIcc θ η).indicator
        (fun _ => 2 * (Real.sqrt (2*Real.pi))⁻¹) x := by
      apply integral_mono hi hj
      intro x
      have hs := thresholdStep_difference_bound θ η x
      by_cases hx : x ∈ uIcc θ η
      · simp only [indicator_of_mem hx, smul_eq_mul]
        calc
          _ ≤ gaussianPDFReal 0 1 x * 2 :=
            mul_le_mul_of_nonneg_left (hb x) (gaussianPDFReal_nonneg _ _ _)
          _ ≤ _ := by linarith [gaussianPDF_standard_le x]
      · simp only [indicator_of_notMem hx] at hs ⊢
        rw [le_antisymm hs (abs_nonneg _), mul_zero]
    _ = _ := by simp [integral_indicator, measurableSet_uIcc, integral_const,
      abs_sub_comm, mul_comm]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.ThresholdSmoothingError
open MeasureTheory ProbabilityTheory Set
open scoped SchwartzMap NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma shifted_threshold_integrable (K : ℝ → ℝ) (hi : Integrable K) (hc : Measurable K)
    (scale θ x : ℝ) : Integrable (fun u => K u * thresholdStep (θ+u/scale) x) := by
  have hm : Measurable (fun u => thresholdStep (θ+u/scale) x) := by
    unfold thresholdStep
    exact measurable_const.ite (measurableSet_le (by fun_prop) measurable_const) measurable_const
  apply hi.norm.mono' (hc.mul hm).aestronglyMeasurable
  exact ae_of_all _ (fun u => by
    simp [Real.norm_eq_abs, abs_mul, thresholdStep_abs])
lemma smoothThreshold_integral (K : ℝ → ℝ) (hi : Integrable K) (hc : Measurable K)
    (hmass : (∫ x, K x) = 1) (scale θ x : ℝ) (hs : 0 < scale) :
    smoothThreshold K scale θ x = ∫ u, K u * thresholdStep (θ+u/scale) x := by
  have he (u : ℝ) : K u * thresholdStep (θ+u/scale) x =
      2 * ((Iic (scale*(x-θ))).indicator K u) - K u := by
    have hh : θ+u/scale ≤ x ↔ u ≤ scale*(x-θ) := by
      rw [← le_sub_iff_add_le', div_le_iff₀ hs]
      constructor <;> intro h <;> nlinarith
    unfold thresholdStep
    by_cases h : u ≤ scale*(x-θ)
    · simp [hh.mpr h, h] <;> ring
    · simp [show ¬ θ+u/scale ≤ x from mt hh.mp h, h] <;> ring
  simp_rw [he]
  rw [integral_sub ((hi.indicator measurableSet_Iic).const_mul 2) hi, integral_const_mul, integral_indicator measurableSet_Iic, hmass]
  rfl
lemma smoothThreshold_error_pointwise (K : 𝓢(ℝ, ℝ))
    (hpos : ∀ u, 0 ≤ K u) (hmass : (∫ u, K u) = 1)
    (scale θ x : ℝ) (hs : 0 < scale) :
    |thresholdStep θ x - smoothThreshold K scale θ x| ≤
      ∫ u, K u * |thresholdStep θ x - thresholdStep (θ+u/scale) x| := by
  have hi := shifted_threshold_integrable K K.integrable K.continuous.measurable scale θ x
  have hconst := (K.integrable (μ := volume)).mul_const (thresholdStep θ x)
  have he : thresholdStep θ x - smoothThreshold K scale θ x =
      ∫ u, K u * (thresholdStep θ x - thresholdStep (θ+u/scale) x) := by
    rw [smoothThreshold_integral K K.integrable K.continuous.measurable hmass scale θ x hs]
    simp_rw [mul_sub]
    rw [integral_sub hconst hi, integral_mul_const, hmass, one_mul]
  rw [he, ← Real.norm_eq_abs]
  convert! norm_integral_le_integral_norm
    (fun u => K u * (thresholdStep θ x - thresholdStep (θ+u/scale) x)) using 1
  congr 1
  funext u
  simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpos u)]
lemma smoothThreshold_gaussian_error (K : 𝓢(ℝ, ℝ))
    (hpos : ∀ u, 0 ≤ K u) (hmass : (∫ u, K u) = 1)
    (scale θ : ℝ) (hs : 0 < scale) :
    (∫ x, |thresholdStep θ x - smoothThreshold K scale θ x| ∂gaussianReal 0 1) ≤
      (2 * (Real.sqrt (2*Real.pi))⁻¹ * (∫ u, |u| * K u)) / scale := by
  let μ := gaussianReal 0 1
  let F : ℝ × ℝ → ℝ := fun z => K z.2 *
    |thresholdStep θ z.1 - thresholdStep (θ+z.2/scale) z.1|
  have hFm : Measurable F := by
    unfold F thresholdStep
    apply Measurable.mul (by fun_prop)
    apply Measurable.abs
    apply Measurable.sub
    · exact measurable_const.ite (measurableSet_le measurable_const measurable_fst) measurable_const
    · exact measurable_const.ite (measurableSet_le (by fun_prop) measurable_fst) measurable_const
  have hbound (x u : ℝ) : |thresholdStep θ x - thresholdStep (θ+u/scale) x| ≤ 2 := by
    calc
      _ ≤ |thresholdStep θ x| + |thresholdStep (θ+u/scale) x| := abs_sub _ _
      _ = _ := by rw [thresholdStep_abs, thresholdStep_abs]; norm_num
  have hFi : Integrable F (μ.prod volume) := by
    have hi := (integrable_const (μ := μ) (2 : ℝ)).mul_prod (K.integrable (μ := volume)).norm
    apply hi.mono' hFm.aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      simp only [F, Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (hpos z.2)]
      nlinarith [hbound z.1 z.2, hpos z.2])
  have hg : Integrable (fun x => |thresholdStep θ x - smoothThreshold K scale θ x|) μ := by
    apply (integrable_const (μ := μ) (2 : ℝ)).mono'
      (((thresholdStep_measurable θ).sub
        (smoothThreshold_contDiff K scale θ).continuous.measurable).abs.aestronglyMeasurable)
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_abs]
      change |thresholdStep θ x - smoothThreshold K scale θ x| ≤ 2
      have h1 := smoothThreshold_abs_le_one K K.integrable hpos hmass scale θ x
      have h2 := abs_sub (thresholdStep θ x) (smoothThreshold K scale θ x)
      rw [thresholdStep_abs] at h2
      linarith)
  have hmoment : Integrable (fun u => |u| * K u) := by
    simpa [Real.norm_eq_abs, hpos, abs_of_nonneg] using K.integrable_pow_mul volume 1
  calc
    _ ≤ ∫ x, ∫ u, F (x,u) ∂volume ∂μ := by
      apply integral_mono hg hFi.integral_prod_left
      intro x
      exact smoothThreshold_error_pointwise K hpos hmass scale θ x hs
    _ = ∫ u, ∫ x, F (x,u) ∂μ := integral_integral_swap hFi
    _ ≤ ∫ u, K u * (2 * (Real.sqrt (2*Real.pi))⁻¹ * |θ-(θ+u/scale)|) := by
      apply integral_mono hFi.integral_prod_right
      · convert! (hmoment.const_mul (2 * (Real.sqrt (2*Real.pi))⁻¹ / scale)) using 1
        funext u
        rw [show θ-(θ+u/scale) = -(u/scale) by ring, abs_neg, abs_div, abs_of_pos hs]
        ring
      · intro u
        dsimp only
        rw [show (∫ x, F (x,u) ∂μ) = K u *
          (∫ x, |thresholdStep θ x - thresholdStep (θ+u/scale) x| ∂μ) by
            exact integral_const_mul (K u) (fun x =>
              |thresholdStep θ x - thresholdStep (θ+u/scale) x|)]
        exact mul_le_mul_of_nonneg_left (gaussian_threshold_translation θ (θ+u/scale)) (hpos u)
    _ = _ := by
      have het (u : ℝ) : θ-(θ+u/scale) = -(u/scale) := by ring
      simp_rw [het, abs_neg, abs_div, abs_of_pos hs]
      have he (u : ℝ) : K u * (2 * (Real.sqrt (2*Real.pi))⁻¹ * (|u|/scale)) =
          (2 * (Real.sqrt (2*Real.pi))⁻¹ / scale) * (|u| * K u) := by ring
      simp_rw [he]
      rw [integral_const_mul]
      ring
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.UniformThresholdSmoothing
open MeasureTheory ProbabilityTheory
open scoped SchwartzMap NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma uniform_threshold_smoothing :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ α : ℝ, 0 < α → α < 1 → ∀ θ : ℝ,
      ∃ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ x, |g x| ≤ 1) ∧
        (∀ n x, |iteratedDeriv n g x| ≤ (C/α)^n) ∧
        (∫ x, |thresholdStep θ x - g x| ∂gaussianReal 0 1) ≤ α/2 := by
  obtain ⟨K,A,B,hA,hB,hpos,hmass,hd⟩ := exists_bandlimited_probability_kernel
  let J := 1 + 2 * (Real.sqrt (2*Real.pi))⁻¹ * (∫ u, |u| * K u)
  let U := (1+2*A)*(1+B)
  have hm : 0 ≤ ∫ u, |u| * K u := integral_nonneg (fun u => mul_nonneg (abs_nonneg _) (hpos u))
  have hJ : 1 ≤ J := by
    dsimp [J]
    linarith [mul_nonneg (show 0 ≤ 2 * (Real.sqrt (2*Real.pi))⁻¹ by positivity) hm]
  have hU : 1 ≤ U := by dsimp [U]; nlinarith
  have hUA : 2*A ≤ U := by dsimp [U]; nlinarith
  have hUB : B ≤ U := by dsimp [U]; nlinarith
  refine ⟨2*J*U, by nlinarith, ?_⟩
  intro α hα hα1 θ
  let scale := 2*J/α
  have hs : 0 < scale := by dsimp [scale]; positivity
  have hs1 : 1 ≤ scale := by
    dsimp [scale]
    rw [le_div_iff₀ hα]
    linarith
  have hH : 1 ≤ U*scale := by nlinarith
  have heq : U*scale = (2*J*U)/α := by dsimp [scale]; ring
  refine ⟨smoothThreshold K scale θ, smoothThreshold_contDiff K scale θ,
    smoothThreshold_abs_le_one K K.integrable hpos hmass scale θ, ?_, ?_⟩
  · intro n x
    rw [← heq]
    cases n with
    | zero => simpa using smoothThreshold_abs_le_one K K.integrable hpos hmass scale θ x
    | succ n =>
      calc
        _ ≤ 2*A*scale^(n+1)*B^n := smoothThreshold_derivative_bound K A B hA.le hB hd scale θ hs.le n x
        _ ≤ U*scale^(n+1)*U^n := by gcongr
        _ = (U*scale)^(n+1) := by rw [mul_pow U scale (n+1), pow_succ U]; ring
  · have h := smoothThreshold_gaussian_error K hpos hmass scale θ hs
    apply h.trans
    rw [div_le_iff₀ hs]
    have he : (α/2)*scale = J := by dsimp [scale]; field_simp <;> ring
    rw [he]
    dsimp [J]
    linarith
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.UnivariateThresholdApproximation
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma univariate_threshold_approximation :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α < 1 → ∀ θ : ℝ,
      ∃ (p : ℕ) (a : ℕ → ℝ),
        (p : ℝ) ≤ C/α^2 ∧ (∑ j ∈ range (p+1), (a j)^2) ≤ 1 ∧
        Integrable (fun x => |thresholdStep θ x - hermitePartial a p x|) (gaussianReal 0 1) ∧
        (∫ x, |thresholdStep θ x - hermitePartial a p x| ∂gaussianReal 0 1) ≤ α := by
  obtain ⟨C0,hC0,hsmooth⟩ := uniform_threshold_smoothing
  let C := 4 * (Real.exp 1 + 2)*C0^2 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro α hα hα1 θ
  obtain ⟨g,hg,hg1,hgd,hge⟩ := hsmooth α hα hα1 θ
  let H := 2*C0/α
  have hH : 1 ≤ H := by
    dsimp [H]
    rw [le_div_iff₀ hα]
    linarith
  have hHD : ∀ n x, |iteratedDeriv n g x| ≤ H^n := by
    intro n x
    apply (hgd n x).trans
    apply pow_le_pow_left₀ (by positivity)
    dsimp [H]
    apply div_le_div_of_nonneg_right _ hα.le
    linarith
  let p := ⌈(Real.exp 1 + 2)*H^2⌉₊
  have hp : (Real.exp 1 + 2)*H^2 ≤ (p : ℝ) := Nat.le_ceil _
  obtain ⟨a,ha,hint,herr⟩ := hermite_projection_approximation g hg hg1 H hH hHD p hp
  have hfirst : Integrable (fun x => |thresholdStep θ x - g x|) (gaussianReal 0 1) := by
    apply (integrable_const (2 : ℝ)).mono'
      (((thresholdStep_measurable θ).sub hg.continuous.measurable).abs.aestronglyMeasurable)
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_abs]
      change |thresholdStep θ x - g x| ≤ 2
      have h := abs_sub (thresholdStep θ x) (g x)
      rw [thresholdStep_abs] at h
      linarith [hg1 x])
  have htotal : Integrable (fun x => |thresholdStep θ x-hermitePartial a p x|) (gaussianReal 0 1) := by
    apply (hfirst.add hint).mono' (by
      exact ((thresholdStep_measurable θ).sub (hermitePartial_continuous a p).measurable).abs.aestronglyMeasurable)
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_abs]
      change |thresholdStep θ x-hermitePartial a p x| ≤
        |thresholdStep θ x-g x|+|g x-hermitePartial a p x|
      exact abs_sub_le _ _ _)
  refine ⟨p,a,?_,ha,htotal,?_⟩
  · have hceil : (p : ℝ) < (Real.exp 1 + 2)*H^2+1 := Nat.ceil_lt_add_one (by positivity)
    apply hceil.le.trans
    rw [le_div_iff₀ (sq_pos_of_pos hα)]
    dsimp [C,H] at *
    have hαsq : α^2 ≤ 1 := by nlinarith
    field_simp
    nlinarith
  · calc
      _ ≤ ∫ x, |thresholdStep θ x-g x|+|g x-hermitePartial a p x| ∂gaussianReal 0 1 :=
        integral_mono htotal (hfirst.add hint) (fun x => abs_sub_le _ _ _)
      _ = (∫ x, |thresholdStep θ x-g x| ∂gaussianReal 0 1)+
          ∫ x, |g x-hermitePartial a p x| ∂gaussianReal 0 1 := integral_add hfirst hint
      _ ≤ α/2+H⁻¹ := add_le_add hge herr
      _ ≤ α := by
        have he : H⁻¹ ≤ α/2 := by
          dsimp [H]
          rw [inv_div, div_le_div_iff₀ (by linarith : 0 < 2*C0) (by norm_num : (0:ℝ)<2)]
          nlinarith
        linarith
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.HermiteLinearLift
open MeasureTheory ProbabilityTheory BookProof.HermiteCore
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma gaussian_unit_inner_preserving {d : ℕ} (u : Vec d) (hu : ‖u‖ = 1) :
    MeasurePreserving (fun x => inner ℝ u x) (gaussian d) (gaussianReal 0 1) := by
  refine ⟨by fun_prop, ?_⟩
  change (stdGaussian (Vec d)).map (innerSL ℝ u) = _
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, innerSL_apply_norm, hu]
  norm_num
noncomputable def linearLiftPoly {d : ℕ} (u : Vec d) : MvPolynomial (Fin d) ℝ :=
  ∑ i, MvPolynomial.C (u i) * MvPolynomial.X i
lemma eval_linearLiftPoly {d : ℕ} (u x : Vec d) :
    MvPolynomial.eval (fun i => x i) (linearLiftPoly u) = inner ℝ u x := by
  simp [linearLiftPoly, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
lemma totalDegree_linearLiftPoly {d : ℕ} (u : Vec d) : (linearLiftPoly u).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro i hi
  simpa only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add] using
    MvPolynomial.totalDegree_mul (MvPolynomial.C (u i)) (MvPolynomial.X i)
noncomputable def hermiteLinearPoly {d : ℕ} (u : Vec d) (n : ℕ) : MvPolynomial (Fin d) ℝ :=
  ∑ k ∈ Finset.range (n+1), MvPolynomial.C ((hermiteR n).coeff k / Real.sqrt (n.factorial : ℝ)) *
    linearLiftPoly u ^ k
lemma eval_hermiteLinearPoly {d : ℕ} (u x : Vec d) (n : ℕ) :
    MvPolynomial.eval (fun i => x i) (hermiteLinearPoly u n) =
      AMPLowDeg.RankOne.hermNorm n (inner ℝ u x) := by
  simp only [hermiteLinearPoly, map_sum, map_mul, map_pow, MvPolynomial.eval_C, eval_linearLiftPoly]
  have hh := Polynomial.eval_eq_sum_range (p := hermiteR n) (inner ℝ u x)
  have hd : (hermiteR n).natDegree = n := by
    rw [hermiteR, Polynomial.natDegree_map_eq_of_injective (Int.cast_injective (α := ℝ)), Polynomial.natDegree_hermite]
  rw [hd] at hh
  change (∑ k ∈ Finset.range (n+1), (hermiteR n).coeff k / Real.sqrt (n.factorial : ℝ) * (inner ℝ u x)^k) =
    (hermiteR n).eval (inner ℝ u x) / Real.sqrt (n.factorial : ℝ)
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← hh]
lemma totalDegree_hermiteLinearPoly {d : ℕ} (u : Vec d) (n : ℕ) :
    (hermiteLinearPoly u n).totalDegree ≤ n := by
  apply (MvPolynomial.totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro k hk
  have hh := MvPolynomial.totalDegree_mul
    (MvPolynomial.C ((hermiteR n).coeff k / Real.sqrt (n.factorial : ℝ)) : MvPolynomial (Fin d) ℝ)
    (linearLiftPoly u ^ k)
  rw [MvPolynomial.totalDegree_C, zero_add] at hh
  exact hh.trans ((MvPolynomial.totalDegree_pow _ _).trans (by
    have hh := totalDegree_linearLiftPoly u
    have hk := Finset.mem_range.mp hk
    nlinarith))
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.HermitePredictorNorm
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma polynomialPredictor_norm_sq (d p : ℕ) (v : Coeff d p) :
    (∫ x, (polynomialPredictor d p v x)^2 ∂gaussian d) = ‖v‖^2 := by
  let h : Index d p → Vec d → ℝ := fun κ => hermite d (fun i => (κ.val i).val)
  have horth := ((lemma_B_8 d).2.2.2 p).2.2
  have hi (κ ξ : Index d p) : Integrable
      (fun x => (v κ*v ξ)*(h κ x*h ξ x)) (gaussian d) :=
    ((horth κ ξ).1).const_mul _
  have he (x : Vec d) : (polynomialPredictor d p v x)^2 =
      ∑ κ : Index d p, ∑ ξ : Index d p, (v κ*v ξ)*(h κ x*h ξ x) := by
    change (inner ℝ v (features d p x))^2 = _
    have hin : inner ℝ v (features d p x) = ∑ κ : Index d p, v κ*h κ x := by
      simp [PiLp.inner_apply, RCLike.inner_apply, features, h, mul_comm]
    rw [hin]
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro κ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ξ _
    ring
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun κ _ => integrable_finsetSum Finset.univ (fun ξ _ => hi κ ξ))]
  simp_rw [integral_finsetSum Finset.univ (fun ξ _ => hi _ ξ), integral_const_mul]
  have ho (κ ξ : Index d p) : (∫ x, h κ x*h ξ x ∂gaussian d) = if κ=ξ then 1 else 0 :=
    (horth κ ξ).2
  simp_rw [ho]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [mul_ite, pow_two]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.HalfspaceApproximation
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma hermitePartial_lift_polynomial {d : ℕ} (u : Vec d) (a : ℕ → ℝ) (p : ℕ) :
    (fun x => hermitePartial a p (inner ℝ u x)) ∈ polynomialFunctions d p := by
  let Q : MvPolynomial (Fin d) ℝ := ∑ j ∈ range (p+1), MvPolynomial.C (a j)*hermiteLinearPoly u j
  refine ⟨Q,?_,?_⟩
  · apply (MvPolynomial.totalDegree_finsetSum _ _).trans
    apply Finset.sup_le
    intro j hj
    have h := MvPolynomial.totalDegree_mul
      (MvPolynomial.C (a j) : MvPolynomial (Fin d) ℝ) (hermiteLinearPoly u j)
    rw [MvPolynomial.totalDegree_C, zero_add] at h
    exact (h.trans (totalDegree_hermiteLinearPoly u j)).trans (by
      have := mem_range.mp hj; omega)
  · intro x
    simp [Q, hermitePartial, eval_hermiteLinearPoly]
lemma polynomial_representation_unitball {d p : ℕ} (f : Vec d → ℝ)
    (hf : f ∈ polynomialFunctions d p) (hn : (∫ x, (f x)^2 ∂gaussian d) ≤ 1) :
    ∃ v : Coeff d p, ‖v‖ ≤ 1 ∧ ∀ x, f x = polynomialPredictor d p v x := by
  rw [((lemma_B_8 d).2.2.2 p).1] at hf
  obtain ⟨v,hv⟩ := hf
  refine ⟨v,?_,?_⟩
  · rw [← hv, polynomialPredictor_norm_sq] at hn
    nlinarith [norm_nonneg v]
  · intro x
    exact congr_fun hv.symm x
lemma affine_label_normalized {d : ℕ} (w : Vec d) (t : ℝ) (hw : w ≠ 0) (x : Vec d) :
    label (affine d w t x) =
      thresholdStep (-t/‖w‖) (inner ℝ (‖w‖⁻¹ • w) x) := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have he : inner ℝ (‖w‖⁻¹ • w) x = inner ℝ w x / ‖w‖ := by
    rw [inner_smul_left, conj_trivial]
    ring
  have hh : (-t/‖w‖ ≤ inner ℝ (‖w‖⁻¹ • w) x) ↔ 0 ≤ inner ℝ w x+t := by
    rw [he, div_le_div_iff_of_pos_right hn]
    constructor <;> intro h <;> linarith
  unfold label affine sign thresholdStep
  simp [hh]
end PrivateAgnosticHalfspace.Gaussian

open PrivateAgnosticHalfspace.Gaussian
 theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (α : ℝ), 0 < α ∧ α < 1 →
      ∀ (w : Vec d) (t : ℝ), ∃ (p : ℕ) (v : Coeff d p),
        (p : ℝ) ≤ C / α ^ 2 ∧ ‖v‖ ≤ 1 ∧
        Integrable (fun x => |label (affine d w t x) - polynomialPredictor d p v x|) (gaussian d) ∧
        (∫ x, |label (affine d w t x) - polynomialPredictor d p v x| ∂gaussian d) ≤ α := by
  obtain ⟨C,hC,happrox⟩ := univariate_threshold_approximation
  refine ⟨C,hC,?_⟩
  intro d hd α hα w t
  letI : IsProbabilityMeasure (gaussian d) := by unfold gaussian; infer_instance
  by_cases hw : w = 0
  · subst w
    let b := label (sign t)
    have hb : b^2 = 1 := by dsimp [b, label]; split_ifs <;> norm_num
    have hf : (fun _ : Vec d => b) ∈ polynomialFunctions d 0 :=
      ⟨MvPolynomial.C b, by simp, by simp⟩
    have hn : (∫ _ : Vec d, b^2 ∂gaussian d) ≤ 1 := by simp [hb]
    obtain ⟨v,hv,hve⟩ := polynomial_representation_unitball (fun _ : Vec d => b) hf hn
    refine ⟨0,v,by simpa only [Nat.cast_zero] using div_nonneg hC.le (sq_nonneg α),hv,?_,?_⟩
    · simp_rw [← hve]
      simp [affine, b]
    · simp_rw [← hve]
      simpa [affine, b] using hα.1.le
  · let u := ‖w‖⁻¹ • w
    have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hu : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hnorm, inv_mul_cancel₀ hnorm.ne']
    let θ := -t/‖w‖
    obtain ⟨p,a,hp,ha,hint,herr⟩ := happrox α hα.1 hα.2 θ
    have hpres := gaussian_unit_inner_preserving u hu
    let f : Vec d → ℝ := fun x => hermitePartial a p (inner ℝ u x)
    have hnormq : (∫ x, (f x)^2 ∂gaussian d) ≤ 1 := by
      calc
        _ = ∫ x, (hermitePartial a p x)^2 ∂gaussianReal 0 1 := by
          rw [← hpres.map_eq, integral_map (by fun_prop)
            (by exact ((hermitePartial_continuous a p).pow 2).aestronglyMeasurable)]
        _ ≤ 1 := by rw [hermitePartial_square_integral]; exact ha
    obtain ⟨v,hv,hve⟩ := polynomial_representation_unitball f
      (hermitePartial_lift_polynomial u a p) hnormq
    have hsign (x : Vec d) : label (affine d w t x) = thresholdStep θ (inner ℝ u x) :=
      affine_label_normalized w t hw x
    refine ⟨p,v,hp,hv,?_,?_⟩
    · simp_rw [← hve, hsign]
      exact (hpres.integrable_comp (by
        exact ((thresholdStep_measurable θ).sub (hermitePartial_continuous a p).measurable).abs.aestronglyMeasurable)).mpr hint
    · simp_rw [← hve, hsign]
      change (∫ x, |thresholdStep θ (inner ℝ u x)-hermitePartial a p (inner ℝ u x)| ∂gaussian d) ≤ α
      rw [← hpres.map_eq, integral_map hpres.measurable.aemeasurable (by
        exact ((thresholdStep_measurable θ).sub (hermitePartial_continuous a p).measurable).abs.aestronglyMeasurable)] at herr
      exact herr
end
