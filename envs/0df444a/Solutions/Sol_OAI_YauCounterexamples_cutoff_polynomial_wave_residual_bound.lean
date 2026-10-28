-- Prove2me | solution 1 for OAI.YauCounterexamples.cutoff_polynomial_wave_residual_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:28:21.596224+00:00
-- url     : https://prove2.me/submissions/8fa51739-f730-467c-8e35-de19352e7d41

import Mathlib
import Definitions.Def_OAIQ070A007

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_WaveDeriv
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples

section WaveDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

theorem waveDeriv_mul (v : E) (f g : E → ℂ) (x : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    waveDeriv v (fun y => f y * g y) x =
      waveDeriv v f x * g x + f x * waveDeriv v g x := by
  simp only [waveDeriv, fderiv_fun_mul hf hg, add_apply, smul_apply, smul_eq_mul]
  ring

theorem waveDeriv_add (v : E) (f g : E → ℂ) (x : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    waveDeriv v (fun y => f y + g y) x = waveDeriv v f x + waveDeriv v g x := by
  simp [waveDeriv, fderiv_fun_add hf hg]

theorem waveDeriv_const_mul (v : E) (c : ℂ) (f : E → ℂ) (x : E)
    (hf : DifferentiableAt ℝ f x) :
    waveDeriv v (fun y => c * f y) x = c * waveDeriv v f x := by
  unfold waveDeriv
  rw [(hf.hasFDerivAt.const_mul c).fderiv]
  rfl

theorem contDiff_waveDeriv (v : E) (f : E → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (waveDeriv v f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem waveDeriv_exp (v : E) (S : E → ℂ) (t : ℂ) (x : E)
    (hS : DifferentiableAt ℝ S x) :
    waveDeriv v (fun y => Complex.exp (t * S y)) x =
      Complex.exp (t * S x) * t * waveDeriv v S x := by
  have hd := ((hS.hasFDerivAt.const_mul t).cexp).fderiv
  dsimp only [waveDeriv]
  rw [hd]
  simp only [smul_apply, smul_eq_mul]
  ring

theorem waveSecondDeriv_exp_mul (v w : E) (S V : E → ℂ) (t : ℂ)
    (hS : ContDiff ℝ ∞ S) (hV : ContDiff ℝ ∞ V) (x : E) :
    waveDeriv v (waveDeriv w (fun y => Complex.exp (t * S y) * V y)) x =
      Complex.exp (t * S x) *
        (t ^ 2 * waveDeriv v S x * waveDeriv w S x * V x +
          t * waveDeriv v (waveDeriv w S) x * V x +
          t * waveDeriv w S x * waveDeriv v V x +
          t * waveDeriv v S x * waveDeriv w V x +
          waveDeriv v (waveDeriv w V) x) := by
  have hSd := hS.differentiable (by simp)
  have hVd := hV.differentiable (by simp)
  have hE : ContDiff ℝ ∞ (fun y => Complex.exp (t * S y)) := (contDiff_const.mul hS).cexp
  have hEd := hE.differentiable (by simp)
  have hSw := (contDiff_waveDeriv w S hS).differentiable (by simp)
  have hVw := (contDiff_waveDeriv w V hV).differentiable (by simp)
  have eq : waveDeriv w (fun y => Complex.exp (t * S y) * V y) =
      fun y => Complex.exp (t * S y) * (t * waveDeriv w S y * V y + waveDeriv w V y) := by
    funext y
    rw [waveDeriv_mul _ _ _ _ (hEd y) (hVd y), waveDeriv_exp _ _ _ _ (hSd y)]
    ring
  rw [eq, waveDeriv_mul v _ (fun y => t * waveDeriv w S y * V y + waveDeriv w V y) x (hEd x)
    ((((hSw x).const_mul t).mul (hVd x)).add (hVw x)),
    waveDeriv_exp _ _ _ _ (hSd x),
    waveDeriv_add v (fun y => t * waveDeriv w S y * V y) (waveDeriv w V) x
      (((hSw x).const_mul t).mul (hVd x)) (hVw x),
    waveDeriv_mul v (fun y => t * waveDeriv w S y) V x ((hSw x).const_mul t) (hVd x),
    waveDeriv_const_mul _ _ _ _ (hSw x)]
  ring

theorem waveCoordinateOperator_exp_mul (e : ι → E) (G : ι → ι → E → ℂ)
    (b : ι → E → ℂ) (S V : E → ℂ) (t : ℂ)
    (hS : ContDiff ℝ ∞ S) (hV : ContDiff ℝ ∞ V) (x : E) :
    waveCoordinateOperator e G b (fun y => Complex.exp (t * S y) * V y) x =
      Complex.exp (t * S x) *
        ((t ^ 2 * waveGradientPair e G S S x + t * waveCoordinateOperator e G b S x) * V x +
          t * (waveGradientPair e G V S x + waveGradientPair e G S V x) +
          waveCoordinateOperator e G b V x) := by
  have hSd := hS.differentiable (by simp)
  have hVd := hV.differentiable (by simp)
  have hEd : Differentiable ℝ (fun y => Complex.exp (t * S y)) :=
    ((contDiff_const.mul hS).cexp).differentiable (by simp)
  simp only [waveCoordinateOperator, waveGradientPair,
    waveSecondDeriv_exp_mul _ _ S V t hS hV x,
    waveDeriv_mul _ _ _ _ (hEd x) (hVd x), waveDeriv_exp _ _ _ _ (hSd x)]
  simp only [mul_add, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul]
  ring_nf
  simp only [mul_assoc, mul_left_comm, mul_comm]
  abel

end WaveDifferentiation


theorem gaussianEnvelope_moment (q : ℕ) (c : ℝ) (hc : 0 < c) (s : ℝ) (hs : 0 ≤ s) :
    s ^ q * Real.exp (s - c * s ^ 2) ≤ (q.factorial : ℝ) * Real.exp (c⁻¹) := by
  have hfac : (0 : ℝ) < q.factorial := by positivity
  have hp : s ^ q ≤ Real.exp s * q.factorial :=
    (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp s hs q)
  have hquad : 2 * s - c * s ^ 2 ≤ c⁻¹ := by
    have h := mul_nonneg hc.le (sq_nonneg (s - c⁻¹))
    have heq : c * (s - c⁻¹) ^ 2 = c * s ^ 2 - 2 * s + c⁻¹ := by
      field_simp
      ring
    rw [heq] at h
    linarith
  calc
    s ^ q * Real.exp (s - c * s ^ 2) ≤
        (Real.exp s * q.factorial) * Real.exp (s - c * s ^ 2) := by
      exact mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = (q.factorial : ℝ) * Real.exp (2 * s - c * s ^ 2) := by
      rw [show 2 * s - c * s ^ 2 = s + (s - c * s ^ 2) by ring, Real.exp_add]
      ring
    _ ≤ (q.factorial : ℝ) * Real.exp (c⁻¹) := by gcongr

theorem gaussianEnvelope_scaled_moment (q : ℕ) (c : ℝ) (hc : 0 < c)
    (n : ℝ) (hn : 0 < n) (r : ℝ) (hr : 0 ≤ r) :
    r ^ q * Real.exp (Real.sqrt n * r - c * n * r ^ 2) ≤
      (q.factorial : ℝ) * Real.exp (c⁻¹) / (Real.sqrt n) ^ q := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  apply (le_div_iff₀ (pow_pos hs q)).2
  have h := gaussianEnvelope_moment q c hc (Real.sqrt n * r) (mul_nonneg hs.le hr)
  have hsq := Real.sq_sqrt hn.le
  calc
    _ = (Real.sqrt n * r) ^ q * Real.exp (Real.sqrt n * r - c * (Real.sqrt n * r) ^ 2) := by
      simp only [mul_pow, hsq]
      ring_nf
    _ ≤ _ := h

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_WaveDerivSum
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι α : Type*} [Fintype ι]

theorem waveDeriv_sum (s : Finset α) (v : E) (f : α → E → ℂ)
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) (x : E) :
    waveDeriv v (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, waveDeriv v (f i) x := by
  simp only [waveDeriv, fderiv_fun_sum (fun i hi => (hf i hi).differentiable (by simp) x),
    sum_apply]

theorem waveCoordinateOperator_sum (s : Finset α) (e : ι → E)
    (G : ι → ι → E → ℂ) (b : ι → E → ℂ) (f : α → E → ℂ)
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) (x : E) :
    waveCoordinateOperator e G b (fun y => ∑ i ∈ s, f i y) x =
      ∑ i ∈ s, waveCoordinateOperator e G b (f i) x := by
  have hd (v : E) : waveDeriv v (fun y => ∑ i ∈ s, f i y) =
      fun y => ∑ i ∈ s, waveDeriv v (f i) y := funext (fun y => waveDeriv_sum s v f hf y)
  simp only [waveCoordinateOperator, hd]
  simp only [waveDeriv_sum s _ _ (fun i hi => contDiff_waveDeriv _ (f i) (hf i hi)), Finset.mul_sum,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm (s:=Finset.univ) (t:=s)]
  congr 1
  simp only [Finset.sum_comm (s:=Finset.univ) (t:=s)]

theorem waveCoordinateOperator_const_mul (e : ι → E)
    (G : ι → ι → E → ℂ) (b : ι → E → ℂ) (c : ℂ) (f : E → ℂ)
    (hf : ContDiff ℝ ∞ f) (x : E) :
    waveCoordinateOperator e G b (fun y => c * f y) x =
      c * waveCoordinateOperator e G b f x := by
  have hd (v : E) : waveDeriv v (fun y => c * f y) = fun y => c * waveDeriv v f y :=
    funext (fun y => waveDeriv_const_mul v c f y (hf.differentiable (by simp) y))
  simp only [waveCoordinateOperator, hd, waveDeriv_const_mul _ _ _ _
    ((contDiff_waveDeriv _ _ hf).differentiable (by simp) x), mul_add,
    Finset.mul_sum, mul_left_comm]

theorem finite_transport_telescope (n : ℂ) (hn : n ≠ 0)
    (t d r : ℕ → ℂ) (h0 : r 0 = t 0)
    (hs : ∀ j, r (j+1) = t (j+1) + d j) (J : ℕ) :
    n * (∑ j ∈ Finset.range (J+1), (n⁻¹)^j * t j) +
      (∑ j ∈ Finset.range (J+1), (n⁻¹)^j * d j) =
    n * (∑ j ∈ Finset.range (J+1), (n⁻¹)^j * r j) + (n⁻¹)^J * d J := by
  induction J with
  | zero => simp [h0]
  | succ J ih =>
    have hp : n * (n⁻¹)^(J+1) = (n⁻¹)^J := by rw [pow_succ]; field_simp
    simp only [Finset.sum_range_succ] at ih ⊢
    rw [hs]
    linear_combination ih - d J * hp

theorem finite_wave_residual (e : ι → E) (G : ι → ι → E → ℂ)
    (b : ι → E → ℂ) (S : E → ℂ) (hS : ContDiff ℝ ∞ S)
    (V : ℕ → E → ℂ) (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (R : ℕ → E → ℂ) (hR0 : R 0 = finiteWaveTransport e G b S (V 0))
    (hRs : ∀ j, R (j+1) = fun x => finiteWaveTransport e G b S (V (j+1)) x +
      waveCoordinateOperator e G b (V j) x)
    (n : ℂ) (hn : n ≠ 0) (J : ℕ) (x : E) :
    let A := fun y => ∑ j ∈ Finset.range (J+1), (n⁻¹)^j * V j y
    waveCoordinateOperator e G b (fun y => Complex.exp (n*S y) * A y) x +
      n*(n+2) * (Complex.exp (n*S x) * A x) =
    Complex.exp (n*S x) *
      (n^2 * (1 + waveGradientPair e G S S x) * A x +
        n * (∑ j ∈ Finset.range (J+1), (n⁻¹)^j * R j x) +
        (n⁻¹)^J * waveCoordinateOperator e G b (V J) x) := by
  dsimp only
  have heq : (fun y => Complex.exp (n*S y) *
      ∑ j ∈ Finset.range (J+1), (n⁻¹)^j * V j y) =
      fun y => ∑ j ∈ Finset.range (J+1), (n⁻¹)^j *
        (Complex.exp (n*S y) * V j y) := by
    funext y
    simp only [Finset.mul_sum]
    congr 1
    funext j
    ring
  have hEV (j : ℕ) : ContDiff ℝ ∞ (fun y => Complex.exp (n*S y) * V j y) :=
    ((contDiff_const.mul hS).cexp).mul (hV j)
  rw [heq, waveCoordinateOperator_sum _ _ _ _ _ (fun j _ => contDiff_const.mul (hEV j))]
  simp only [waveCoordinateOperator_const_mul _ _ _ _ _ (hEV _), waveCoordinateOperator_exp_mul _ _ _ _ _ _ hS (hV _)]
  have ht := finite_transport_telescope n hn
    (fun j => finiteWaveTransport e G b S (V j) x)
    (fun j => waveCoordinateOperator e G b (V j) x) (fun j => R j x)
    (congrFun hR0 x) (fun j => congrFun (hRs j) x) J
  dsimp only [finiteWaveTransport] at ht
  simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add, add_mul] at ht ⊢
  linear_combination (norm := skip) Complex.exp (n*S x) * ht
  ring_nf
  simp only [Finset.mul_sum]
  ring_nf

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_MultilinearPolynomial
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma iteratedFDeriv_eq_directionalJet {f : E → F} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (v : Fin n → E) (x : E) :
    iteratedFDeriv ℝ n f x v = directionalJet (List.ofFn v) f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hd := hf.differentiable_iteratedFDeriv
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) x
    rw [hd.iteratedFDeriv_succ_apply_left', List.ofFn_succ, directionalJet_cons]
    congr 2
    funext y
    exact ih (Fin.tail v) y


end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff

open MvPolynomial
variable {σ : Type*}

variable [Fintype σ]

theorem contDiff_realPolyEval (p : MvPolynomial σ ℂ) : ContDiff ℝ ∞ (realPolyEval p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [show realPolyEval (C c : MvPolynomial σ ℂ) = fun _ => c by funext x; exact realPolyEval_C c x]
    exact contDiff_const
  | add p q hp hq =>
    rw [show realPolyEval (p + q) = fun x => realPolyEval p x + realPolyEval q x by funext x; exact realPolyEval_add p q x]
    exact hp.add hq
  | mul_X p i hp =>
    have hx : ContDiff ℝ ∞ (fun x : σ → ℝ => (x i : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ).contDiff
    rw [show realPolyEval (p * X i) = fun x => realPolyEval p x * (x i : ℂ) by funext x; simp]
    exact hp.mul hx

theorem fderiv_realPolyEval (p : MvPolynomial σ ℂ) (x v : σ → ℝ) :
    fderiv ℝ (realPolyEval p) x v =
      ∑ i, (v i : ℂ) * realPolyEval (pderiv i p) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c =>
    have heq : realPolyEval (C c : MvPolynomial σ ℂ) = fun _ => c := by ext x; exact realPolyEval_C c x
    rw [heq]
    simp
  | add p q hp hq =>
    have h := fderiv_add ((contDiff_realPolyEval p).differentiable (by simp) x)
      ((contDiff_realPolyEval q).differentiable (by simp) x)
    rw [show realPolyEval (p + q) = realPolyEval p + realPolyEval q by ext; simp, h]
    simp only [add_apply, hp, hq, map_add,
      realPolyEval_add, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    have hcoord : HasFDerivAt (fun x : σ → ℝ => (x j : ℂ))
        (Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_apply j x)
    rw [show realPolyEval (p * X j) = fun x => realPolyEval p x * (x j : ℂ) by ext; simp,
      fderiv_fun_mul ((contDiff_realPolyEval p).differentiable (by simp) x)
        hcoord.differentiableAt, hcoord.fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply,
      smul_eq_mul, hp, pderiv_mul, realPolyEval_add, realPolyEval_mul, realPolyEval_X,
      pderiv_X, Pi.single_apply, mul_add, Finset.sum_add_distrib]
    have hif (i : σ) : realPolyEval (if j = i then 1 else 0) x =
        if j = i then 1 else 0 := by split_ifs <;> simp
    simp only [hif, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [← mul_assoc, ← Finset.sum_mul]
    ring


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_BoundedDegreeMonomials
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SmoothJetZero
lemma mono {f : E → F} {N M : ℕ} (h : SmoothJetZero f N) (hMN : M ≤ N) :
    SmoothJetZero f M := fun k hk => h k (hk.trans_le hMN)

end SmoothJetZero

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem vanishing_jet_norm_bound (f : E → F) (hf : ContDiff ℝ ∞ f)
    (N : ℕ) (r C : ℝ) (hC : 0 ≤ C)
    (hzero : ∀ j < N, iteratedFDeriv ℝ j f 0 = 0)
    (hbound : ∀ x ∈ Metric.ball (0 : E) r, ‖iteratedFDeriv ℝ N f x‖ ≤ C) :
    ∀ k ≤ N, ∀ x ∈ Metric.ball (0 : E) r,
      ‖iteratedFDeriv ℝ (N - k) f x‖ ≤ C * ‖x‖ ^ k := by
  intro k
  induction k with
  | zero =>
    intro _ x hx
    simpa using hbound x hx
  | succ k ih =>
    intro hk x hx
    have hxnorm : ‖x‖ < r := by simpa using hx
    have hyball : ∀ y ∈ Metric.closedBall (0 : E) ‖x‖, y ∈ Metric.ball (0 : E) r := by
      intro y hy
      have hxy : ‖y‖ ≤ ‖x‖ := by simpa using hy
      simpa using hxy.trans_lt hxnorm
    have hd : ∀ y ∈ Metric.closedBall (0 : E) ‖x‖,
        DifferentiableAt ℝ (iteratedFDeriv ℝ (N - (k + 1)) f) y := by
      intro y _
      exact hf.differentiable_iteratedFDeriv (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (N - (k + 1)))) y
    have hb : ∀ y ∈ Metric.closedBall (0 : E) ‖x‖,
        ‖fderiv ℝ (iteratedFDeriv ℝ (N - (k + 1)) f) y‖ ≤ C * ‖x‖ ^ k := by
      intro y hy
      rw [norm_fderiv_iteratedFDeriv, show N - (k + 1) + 1 = N - k by omega]
      have h := ih (by omega) y (hyball y hy)
      have hxy : ‖y‖ ≤ ‖x‖ := by simpa using hy
      exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hxy _) hC)
    have hm := (convex_closedBall (0 : E) ‖x‖).norm_image_sub_le_of_norm_fderiv_le hd hb
      (Metric.mem_closedBall_self (norm_nonneg x))
      (show x ∈ Metric.closedBall (0 : E) ‖x‖ by simp)
    rw [hzero (N - (k + 1)) (by omega), sub_zero, sub_zero] at hm
    simpa only [pow_succ, mul_assoc] using hm


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PolynomialFiniteWave
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma waveDeriv_realPolyEval_single (i : σ) (P : MvPolynomial σ ℂ) :
    waveDeriv (Pi.single i 1) (realPolyEval P) = realPolyEval (pderiv i P) := by
  funext x
  simp [waveDeriv, fderiv_realPolyEval, Pi.single_apply, apply_ite]

lemma smoothPolynomialLaplacian_eq_operator (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (P : MvPolynomial σ ℂ) :
    smoothPolynomialLaplacian g b P =
      waveCoordinateOperator (fun i => Pi.single i 1) g b (realPolyEval P) := by
  funext x
  simp only [waveCoordinateOperator, waveDeriv_realPolyEval_single,
    smoothPolynomialLaplacian]

omit [DecidableEq σ] in
lemma sum_transport_product (G : σ → σ → ℂ) (s v : σ → ℂ) :
    (∑ i, (∑ j, (G i j + G j i) * s j) * v i) =
      (∑ i, ∑ j, G i j * v i * s j) + (∑ i, ∑ j, G i j * s i * v j) := by
  simp only [Finset.sum_mul, add_mul, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · rw [Finset.sum_comm]

lemma smoothWaveTransport_eq_finite (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (S V : MvPolynomial σ ℂ) :
    smoothWaveTransport (smoothPhaseTransportVector g S)
      (smoothPhaseTransportScalar g b S) V =
    finiteWaveTransport (fun i => Pi.single i 1) g b (realPolyEval S) (realPolyEval V) := by
  funext x
  simp only [smoothWaveTransport, smoothPhaseTransportVector, smoothPhaseTransportScalar,
    finiteWaveTransport, waveGradientPair, waveDeriv_realPolyEval_single,
    ← smoothPolynomialLaplacian_eq_operator]
  rw [sum_transport_product]



end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma smoothEikonalResidual_eq_gradientPair (g : σ → σ → (σ → ℝ) → ℂ)
    (S : MvPolynomial σ ℂ) :
    smoothEikonalResidual g S = fun x =>
      1 + waveGradientPair (fun i => Pi.single i 1) g (realPolyEval S) (realPolyEval S) x := by
  funext x
  simp only [smoothEikonalResidual, waveGradientPair, waveDeriv_realPolyEval_single]

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_NormIteratedFDerivConstMul
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff

lemma directionalJet_cexp (l : List ℂ) :
    directionalJet l Complex.exp = fun z => Complex.exp z * l.prod := by
  induction l with
  | nil => funext z; simp
  | cons v l ih =>
    rw [directionalJet_cons,ih]
    funext z
    have hd := ((hasFDerivAt_id (𝕜 := ℝ) z).cexp).mul_const l.prod
    change HasFDerivAt (fun y : ℂ => Complex.exp y * l.prod) _ z at hd
    rw [hd.fderiv]
    simp [List.prod_cons, mul_assoc,mul_comm,mul_left_comm]

lemma norm_real_iteratedFDeriv_cexp_le (k : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ k Complex.exp z‖ ≤ Real.exp z.re := by
  apply ContinuousMultilinearMap.opNorm_le_bound (Real.exp_pos _).le
  intro v
  rw [iteratedFDeriv_eq_directionalJet Complex.contDiff_exp,
    directionalJet_cexp]
  simp [Complex.norm_exp,List.prod_ofFn]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem semiclassical_exponential_jet_bound (S : E → ℂ) (hS : ContDiff ℝ ∞ S)
    (k : ℕ) (x : E) (C n : ℝ) (hC : 1 ≤ C) (hn : 1 ≤ n)
    (hjets : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i S x‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (fun y => Complex.exp ((n : ℂ) * S y)) x‖ ≤
      (k.factorial : ℝ) * C ^ k * n ^ k * Real.exp (n * (S x).re) := by
  have hCd : 0 ≤ C := le_trans zero_le_one hC
  have hnd : 0 ≤ n := le_trans zero_le_one hn
  have hcomp := norm_iteratedFDeriv_comp_le Complex.contDiff_exp
    (hS.const_smul (n : ℂ))
    (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))) x
    (C := Real.exp (n * (S x).re)) (D := n * C)
    (fun i _ => by simpa using norm_real_iteratedFDeriv_cexp_le i ((n : ℂ) * S x))
    (fun i hi hik => by
      rw [iteratedFDeriv_const_smul_apply'
        ((hS.of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top i))))).contDiffAt,
        norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnd]
      calc
        n * ‖iteratedFDeriv ℝ i S x‖ ≤ n * C := mul_le_mul_of_nonneg_left (hjets i hi hik) hnd
        _ ≤ (n * C) ^ i := le_self_pow₀ (one_le_mul_of_one_le_of_one_le hn hC) (by omega))
  simpa only [smul_eq_mul,Function.comp_def,mul_pow] using hcomp.trans_eq (by ring)

lemma expJetConstant_nonneg (k : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ expJetConstant k C := by
  unfold expJetConstant
  positivity

theorem semiclassical_product_jet_bound (S F : E → ℂ)
    (hS : ContDiff ℝ ∞ S) (hF : ContDiff ℝ ∞ F)
    (k : ℕ) (x : E) (C A n : ℝ) (hC : 1 ≤ C) (_hA : 0 ≤ A) (hn : 1 ≤ n)
    (hSjets : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i S x‖ ≤ C)
    (hFjets : ∀ i ≤ k, ‖iteratedFDeriv ℝ i F x‖ ≤ A) :
    ‖iteratedFDeriv ℝ k (fun y => Complex.exp ((n : ℂ) * S y) * F y) x‖ ≤
      expJetConstant k C * A * n ^ k * Real.exp (n * (S x).re) := by
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  have hExp := Real.exp_pos (n * (S x).re)
  have hb := norm_iteratedFDeriv_mul_le
    ((hS.const_smul (n:ℂ)).cexp) hF x
    (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))
  apply hb.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1),
        (k.choose i : ℝ) * ((i.factorial : ℝ) * C ^ i * n ^ k * Real.exp (n * (S x).re)) * A := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply (semiclassical_exponential_jet_bound S hS i x C n hC hn
          (fun j hj hji => hSjets j hj (hji.trans hik))).trans
        gcongr
      · exact hFjets (k-i) (Nat.sub_le _ _)
      · exact norm_nonneg _
      · positivity
    _ = _ := by
      unfold expJetConstant
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem localized_product_jet_bound (S F : E → ℂ)
    (hS : ContDiff ℝ ∞ S) (hF : ContDiff ℝ ∞ F)
    (k q : ℕ) (x : E) (C A n φ c : ℝ) (hC : 1 ≤ C) (hA : 0 ≤ A)
    (hn : 1 ≤ n) (hc : 0 < c)
    (hSjets : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i S x‖ ≤ C)
    (hFjets : ∀ i ≤ k, ‖iteratedFDeriv ℝ i F x‖ ≤ A * ‖x‖ ^ q)
    (hphase : n * ((S x).re - φ) ≤ Real.sqrt n * ‖x‖ - c * n * ‖x‖ ^ 2) :
    ‖iteratedFDeriv ℝ k (fun y => Complex.exp ((n : ℂ) * S y) * F y) x‖ ≤
      expJetConstant k C * A * n ^ k *
        ((q.factorial : ℝ) * Real.exp c⁻¹ / (Real.sqrt n) ^ q) * Real.exp (n * φ) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have he : Real.exp (n * (S x).re) ≤
      Real.exp (n * φ) * Real.exp (Real.sqrt n * ‖x‖ - c * n * ‖x‖ ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hb := semiclassical_product_jet_bound S F hS hF k x C (A * ‖x‖ ^ q) n hC
    (mul_nonneg hA (pow_nonneg (norm_nonneg _) _)) hn hSjets hFjets
  have hmoment := gaussianEnvelope_scaled_moment q c hc n hn0 ‖x‖ (norm_nonneg _)
  have hconst : 0 ≤ expJetConstant k C * A * n ^ k := by
    exact mul_nonneg (mul_nonneg (expJetConstant_nonneg k (zero_le_one.trans hC)) hA)
      (pow_nonneg hn0.le _)
  calc
    _ ≤ expJetConstant k C * (A * ‖x‖ ^ q) * n ^ k * Real.exp (n * (S x).re) := hb
    _ ≤ expJetConstant k C * (A * ‖x‖ ^ q) * n ^ k *
        (Real.exp (n * φ) * Real.exp (Real.sqrt n * ‖x‖ - c * n * ‖x‖ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left he
      convert mul_nonneg hconst (pow_nonneg (norm_nonneg x) q) using 1 <;> first | rfl | ring
    _ = (expJetConstant k C * A * n ^ k) *
        (‖x‖ ^ q * Real.exp (Real.sqrt n * ‖x‖ - c * n * ‖x‖ ^ 2)) * Real.exp (n * φ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmoment hconst)
      (Real.exp_pos _).le

theorem common_vanishing_jet_bound (F : E → ℂ) (hF : ContDiff ℝ ∞ F)
    (K m : ℕ) (hm : m ≤ K) (r A : ℝ) (hr : r ≤ 1) (hA : 0 ≤ A)
    (hzero : ∀ j < K, iteratedFDeriv ℝ j F 0 = 0)
    (hbound : ∀ x ∈ Metric.ball (0 : E) r, ‖iteratedFDeriv ℝ K F x‖ ≤ A) :
    ∀ x ∈ Metric.ball (0 : E) r, ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j F x‖ ≤ A * ‖x‖ ^ (K-m) := by
  intro x hx j hj
  have hjK : j ≤ K := hj.trans hm
  have hb := vanishing_jet_norm_bound F hF K r A hA hzero hbound
    (K-j) (Nat.sub_le _ _) x hx
  rw [Nat.sub_sub_self hjK] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ hA
  exact pow_le_pow_of_le_one (norm_nonneg _) ((by simpa using hx : ‖x‖ < r).le.trans hr)
    (Nat.sub_le_sub_left hj K)

lemma semiclassical_power_cancellation (n : ℝ) (hn : 0 < n) (a b : ℕ) :
    n ^ a / (Real.sqrt n) ^ (2*(a+b)) = (n ^ b)⁻¹ := by
  rw [pow_mul,Real.sq_sqrt hn.le,pow_add]
  field_simp

theorem scheduled_taylor_wave_bound (S F : E → ℂ)
    (hS : ContDiff ℝ ∞ S) (hF : ContDiff ℝ ∞ F)
    (m D : ℕ) (x : E) (C A n φ c r : ℝ)
    (hC : 1 ≤ C) (hA : 0 ≤ A) (hn : 1 ≤ n) (hc : 0 < c) (hr : r ≤ 1)
    (hx : x ∈ Metric.ball (0 : E) r)
    (hSjets : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i S x‖ ≤ C)
    (hzero : ∀ j < 2*D+3*m+6, iteratedFDeriv ℝ j F 0 = 0)
    (hbound : ∀ y ∈ Metric.ball (0 : E) r,
      ‖iteratedFDeriv ℝ (2*D+3*m+6) F y‖ ≤ A)
    (hphase : n * ((S x).re - φ) ≤ Real.sqrt n * ‖x‖ - c * n * ‖x‖ ^ 2) :
    ‖iteratedFDeriv ℝ m (fun y => Complex.exp ((n : ℂ) * S y) * F y) x‖ ≤
      (expJetConstant m C * A * ((2*(m+(D+3))).factorial : ℝ) * Real.exp c⁻¹) *
        (n ^ (D+3))⁻¹ * Real.exp (n * φ) := by
  have hq : 2*D+3*m+6-m = 2*(m+(D+3)) := by omega
  have hFj := common_vanishing_jet_bound F hF (2*D+3*m+6) m (by omega)
    r A hr hA hzero hbound x hx
  rw [hq] at hFj
  apply (localized_product_jet_bound S F hS hF m (2*(m+(D+3))) x C A n φ c
    hC hA hn hc hSjets hFj hphase).trans_eq
  have hp := semiclassical_power_cancellation n (zero_lt_one.trans_le hn) m (D+3)
  calc
    _ = (expJetConstant m C * A * ((2*(m+(D+3))).factorial : ℝ) * Real.exp c⁻¹) *
        (n ^ m / (Real.sqrt n) ^ (2*(m+(D+3)))) * Real.exp (n * φ) := by ring
    _ = _ := by rw [hp]

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_iteratedFDeriv_const_mul (c : ℂ) (F : E → ℂ) (hF : ContDiff ℝ ∞ F)
    (m : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ m (fun y => c * F y) x‖ = ‖c‖ * ‖iteratedFDeriv ℝ m F x‖ := by
  change ‖iteratedFDeriv ℝ m (fun y => c • F y) x‖ = _
  rw [iteratedFDeriv_const_smul_apply'
    ((hF.of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m))))).contDiffAt,
    norm_smul]

lemma norm_iteratedFDeriv_add_le (F G : E → ℂ) (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (m : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ m (fun y => F y + G y) x‖ ≤
      ‖iteratedFDeriv ℝ m F x‖ + ‖iteratedFDeriv ℝ m G x‖ := by
  change ‖iteratedFDeriv ℝ m (F+G) x‖ ≤ _
  rw [iteratedFDeriv_add_apply
    ((hF.of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m))))).contDiffAt
    ((hG.of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m))))).contDiffAt]
  exact norm_add_le _ _

lemma norm_iteratedFDeriv_linear_three (F G H : E → ℂ)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (c d e : ℂ) (m : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ m (fun y => c*F y+d*G y+e*H y) x‖ ≤
      ‖c‖*‖iteratedFDeriv ℝ m F x‖ + ‖d‖*‖iteratedFDeriv ℝ m G x‖ +
        ‖e‖*‖iteratedFDeriv ℝ m H x‖ := by
  have hc : ContDiff ℝ ∞ (fun y => c*F y) := contDiff_const.mul hF
  have hd : ContDiff ℝ ∞ (fun y => d*G y) := contDiff_const.mul hG
  have he : ContDiff ℝ ∞ (fun y => e*H y) := contDiff_const.mul hH
  calc
    _ ≤ ‖iteratedFDeriv ℝ m (fun y => c*F y+d*G y) x‖ +
        ‖iteratedFDeriv ℝ m (fun y => e*H y) x‖ :=
      norm_iteratedFDeriv_add_le _ _ (hc.add hd) he m x
    _ ≤ (‖iteratedFDeriv ℝ m (fun y => c*F y) x‖ +
          ‖iteratedFDeriv ℝ m (fun y => d*G y) x‖) +
        ‖iteratedFDeriv ℝ m (fun y => e*H y) x‖ :=
      add_le_add (norm_iteratedFDeriv_add_le _ _ hc hd m x) le_rfl
    _ = _ := by rw [norm_iteratedFDeriv_const_mul c F hF,
      norm_iteratedFDeriv_const_mul d G hG, norm_iteratedFDeriv_const_mul e H hH]

lemma norm_iteratedFDeriv_weighted_sum (F : ℕ → E → ℂ)
    (hF : ∀ j, ContDiff ℝ ∞ (F j)) (J m : ℕ) (x : E) (t : ℂ) (ht : ‖t‖ ≤ 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ j ≤ J, ‖iteratedFDeriv ℝ m (F j) x‖ ≤ A) :
    ‖iteratedFDeriv ℝ m (fun y => ∑ j ∈ Finset.range (J+1), t^j * F j y) x‖ ≤
      (J+1 : ℕ) * A := by
  rw [iteratedFDeriv_fun_sum_apply (fun j _ =>
    ((contDiff_const.mul (hF j)).of_le
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m)))).contDiffAt)]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (J+1), A := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_iteratedFDeriv_const_mul _ _ (hF j), norm_pow]
      exact (mul_le_mul_of_nonneg_left (hbound j (by simpa using hj))
        (pow_nonneg (norm_nonneg _) _)).trans
        ((mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) ht) hA).trans_eq
          (one_mul A))
    _ = _ := by simp

lemma inverse_frequency_norm_le_one {n : ℝ} (hn : 1 ≤ n) : ‖((n : ℂ)⁻¹)‖ ≤ 1 := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans_le hn)]
  exact inv_le_one_of_one_le₀ hn

lemma frequency_schedule_cancellation {n : ℝ} (hn : 0 < n) (a b : ℕ) :
    n^a * (n^(a+b))⁻¹ = (n^b)⁻¹ := by
  rw [pow_add]
  field_simp

lemma frequency_inverse_power_mono {n : ℝ} (hn : 1 ≤ n) {a b : ℕ} (hab : a ≤ b) :
    (n^b)⁻¹ ≤ (n^a)⁻¹ := by
  apply inv_anti₀ (pow_pos (zero_lt_one.trans_le hn) a)
  exact pow_le_pow_right₀ hn hab

lemma bounded_wave_term (S F : E → ℂ) (hS : ContDiff ℝ ∞ S) (hF : ContDiff ℝ ∞ F)
    (m : ℕ) (x : E) (C A n φ c : ℝ) (hC : 1 ≤ C) (hA : 0 ≤ A)
    (hn : 1 ≤ n) (hc : 0 < c)
    (hSjets : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i S x‖ ≤ C)
    (hFjets : ∀ i ≤ m, ‖iteratedFDeriv ℝ i F x‖ ≤ A)
    (hphase : n * ((S x).re - φ) ≤ Real.sqrt n * ‖x‖ - c*n*‖x‖^2) :
    ‖iteratedFDeriv ℝ m (fun y => Complex.exp ((n : ℂ)*S y)*F y) x‖ ≤
      expJetConstant m C * A * Real.exp c⁻¹ * n^m * Real.exp (n*φ) := by
  have hb := localized_product_jet_bound S F hS hF m 0 x C A n φ c
    hC hA hn hc hSjets (by simpa using hFjets) hphase
  simpa [mul_assoc, mul_left_comm, mul_comm] using hb

theorem finite_scheduled_residual_bound
    (S : E → ℂ) (F R : ℕ → E → ℂ) (L : E → ℂ)
    (hS : ContDiff ℝ ∞ S) (hF : ∀ j, ContDiff ℝ ∞ (F j))
    (hR : ∀ j, ContDiff ℝ ∞ (R j)) (hL : ContDiff ℝ ∞ L)
    (m D J : ℕ) (hJ : D+m+1 ≤ J) (x : E) (C A n φ c r : ℝ)
    (hC : 1 ≤ C) (hA : 0 ≤ A) (hn : 1 ≤ n) (hc : 0 < c) (hr : r ≤ 1)
    (hx : x ∈ Metric.ball (0 : E) r)
    (hSjets : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i S x‖ ≤ C)
    (hFzero : ∀ j ≤ J, SmoothJetZero (F j) (2*D+3*m+6))
    (hRzero : ∀ j ≤ J, SmoothJetZero (R j) (2*D+3*m+6))
    (hFbound : ∀ j ≤ J, ∀ y ∈ Metric.ball (0 : E) r,
      ‖iteratedFDeriv ℝ (2*D+3*m+6) (F j) y‖ ≤ A)
    (hRbound : ∀ j ≤ J, ∀ y ∈ Metric.ball (0 : E) r,
      ‖iteratedFDeriv ℝ (2*D+3*m+6) (R j) y‖ ≤ A)
    (hLbound : ∀ i ≤ m, ‖iteratedFDeriv ℝ i L x‖ ≤ A)
    (hphase : n * ((S x).re - φ) ≤ Real.sqrt n * ‖x‖ - c*n*‖x‖^2) :
    let H := fun y => (n : ℂ)^2 *
        (∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j * (Complex.exp ((n : ℂ)*S y)*F j y)) +
      (n : ℂ) * (∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j *
        (Complex.exp ((n : ℂ)*S y)*R j y)) +
      ((n : ℂ)⁻¹)^J * (Complex.exp ((n : ℂ)*S y)*L y)
    let T := expJetConstant m C * A * ((2*(m+(D+3))).factorial : ℝ) * Real.exp c⁻¹
    ‖iteratedFDeriv ℝ m H x‖ ≤
      (2*(J+1 : ℕ)*T + expJetConstant m C*A*Real.exp c⁻¹) *
        (n^(D+1))⁻¹ * Real.exp (n*φ) := by
  dsimp only
  let T := expJetConstant m C * A * ((2*(m+(D+3))).factorial : ℝ) * Real.exp c⁻¹
  let U := expJetConstant m C * A * Real.exp c⁻¹
  let V := Real.exp (n*φ)
  have hn0 := zero_lt_one.trans_le hn
  have hnn : ‖(n : ℂ)‖ = n := by simp [abs_of_pos hn0]
  have hT : 0 ≤ T := by
    dsimp [T]; exact mul_nonneg (mul_nonneg
      (mul_nonneg (expJetConstant_nonneg _ (zero_le_one.trans hC)) hA)
      (Nat.cast_nonneg _)) (Real.exp_pos _).le
  have hU : 0 ≤ U := mul_nonneg
    (mul_nonneg (expJetConstant_nonneg _ (zero_le_one.trans hC)) hA) (Real.exp_pos _).le
  have hV : 0 < V := Real.exp_pos _
  have he : ContDiff ℝ ∞ (fun y => Complex.exp ((n : ℂ)*S y)) :=
    (contDiff_const.mul hS).cexp
  have hEF (j : ℕ) : ContDiff ℝ ∞ (fun y => Complex.exp ((n : ℂ)*S y)*F j y) := he.mul (hF j)
  have hER (j : ℕ) : ContDiff ℝ ∞ (fun y => Complex.exp ((n : ℂ)*S y)*R j y) := he.mul (hR j)
  have hEL : ContDiff ℝ ∞ (fun y => Complex.exp ((n : ℂ)*S y)*L y) := he.mul hL
  have hFS := norm_iteratedFDeriv_weighted_sum _ hEF J m x
    ((n : ℂ)⁻¹) (inverse_frequency_norm_le_one hn) (T * (n^(D+3))⁻¹ * V)
    (by positivity) (fun j hj => scheduled_taylor_wave_bound S (F j) hS (hF j)
      m D x C A n φ c r hC hA hn hc hr hx hSjets (hFzero j hj) (hFbound j hj) hphase)
  have hRS := norm_iteratedFDeriv_weighted_sum _ hER J m x
    ((n : ℂ)⁻¹) (inverse_frequency_norm_le_one hn) (T * (n^(D+3))⁻¹ * V)
    (by positivity) (fun j hj => scheduled_taylor_wave_bound S (R j) hS (hR j)
      m D x C A n φ c r hC hA hn hc hr hx hSjets (hRzero j hj) (hRbound j hj) hphase)
  have hLB := bounded_wave_term S L hS hL m x C A n φ c hC hA hn hc hSjets hLbound hphase
  have hSF : ContDiff ℝ ∞ (fun y => ∑ j ∈ Finset.range (J+1),
      ((n : ℂ)⁻¹)^j * (Complex.exp ((n : ℂ)*S y)*F j y)) :=
    ContDiff.sum (fun j _ => contDiff_const.mul (hEF j))
  have hSR : ContDiff ℝ ∞ (fun y => ∑ j ∈ Finset.range (J+1),
      ((n : ℂ)⁻¹)^j * (Complex.exp ((n : ℂ)*S y)*R j y)) :=
    ContDiff.sum (fun j _ => contDiff_const.mul (hER j))
  have htri := norm_iteratedFDeriv_linear_three _ _ _ hSF hSR hEL
    ((n : ℂ)^2) (n : ℂ) (((n : ℂ)⁻¹)^J) m x
  apply htri.trans
  rw [norm_pow, norm_pow, norm_inv, hnn]
  have hb1 := mul_le_mul_of_nonneg_left hFS (pow_nonneg hn0.le 2)
  have hb2 := mul_le_mul_of_nonneg_left hRS hn0.le
  have hb3 := mul_le_mul_of_nonneg_left hLB (pow_nonneg (inv_nonneg.mpr hn0.le) J)
  apply (add_le_add (add_le_add hb1 hb2) hb3).trans
  have hc1 : n^2 * (n^(D+3))⁻¹ = (n^(D+1))⁻¹ := by
    simpa only [show 2+(D+1)=D+3 by omega] using frequency_schedule_cancellation hn0 2 (D+1)
  have hc2 : n * (n^(D+3))⁻¹ ≤ (n^(D+1))⁻¹ := by
    calc
      n * (n^(D+3))⁻¹ ≤ n^2 * (n^(D+3))⁻¹ := by gcongr; exact le_self_pow₀ hn (by omega)
      _ = _ := hc1
  have hc3 : (n⁻¹)^J * n^m ≤ (n^(D+1))⁻¹ := by
    rw [inv_pow]
    calc
      _ ≤ (n^(m+(D+1)))⁻¹ * n^m := by
        exact mul_le_mul_of_nonneg_right
          (frequency_inverse_power_mono hn (by omega)) (pow_nonneg hn0.le _)
      _ = _ := by rw [mul_comm]; exact frequency_schedule_cancellation hn0 m (D+1)
  change n^2 * ((J+1 : ℕ) * (T * (n^(D+3))⁻¹ * V)) +
      n * ((J+1 : ℕ) * (T * (n^(D+3))⁻¹ * V)) +
      (n⁻¹)^J * (U*n^m*V) ≤ _
  calc
    _ = (J+1 : ℕ)*T*V*(n^2*(n^(D+3))⁻¹) +
        (J+1 : ℕ)*T*V*(n*(n^(D+3))⁻¹) + U*V*((n⁻¹)^J*n^m) := by ring
    _ ≤ (J+1 : ℕ)*T*V*(n^(D+1))⁻¹ +
        (J+1 : ℕ)*T*V*(n^(D+1))⁻¹ + U*V*(n^(D+1))⁻¹ := by
      rw [hc1]
      have hh : (J+1 : ℕ)*T*V*(n*(n^(D+3))⁻¹) ≤
          (J+1 : ℕ)*T*V*(n^(D+1))⁻¹ :=
        mul_le_mul_of_nonneg_left hc2 (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hT) hV.le)
      exact add_le_add (add_le_add le_rfl hh)
        (mul_le_mul_of_nonneg_left hc3 (mul_nonneg hU hV.le))
    _ = _ := by dsimp [T,U,V]; ring


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SmoothFiniteWaveSum
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
section UniformJetBounds
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma UniformJetBounds.mono {f : X → E → ℂ} {K K' : Set X} {B B' : Set E}
    (h : UniformJetBounds f K B) (hK : K' ⊆ K) (hB : B' ⊆ B) :
    UniformJetBounds f K' B' := by
  intro k
  obtain ⟨C,hC,h⟩ := h k
  exact ⟨C,hC,fun p hp x hx => h p (hK hp) x (hB hx)⟩

lemma UniformJetBounds.const (c : ℂ) (K : Set X) (B : Set E) :
    UniformJetBounds (fun _ _ => c) K B := by
  intro k
  refine ⟨‖c‖+1,by positivity,?_⟩
  intro p hp x hx
  cases k with
  | zero => simp
  | succ k => simp [iteratedFDeriv_succ_const]; positivity

lemma UniformJetBounds.add {f g : X → E → ℂ} {K : Set X} {B : Set E}
    (hf : ∀ p, ContDiff ℝ ∞ (f p)) (hg : ∀ p, ContDiff ℝ ∞ (g p))
    (hfB : UniformJetBounds f K B) (hgB : UniformJetBounds g K B) :
    UniformJetBounds (fun p x => f p x + g p x) K B := by
  intro k
  obtain ⟨C,hC,hCb⟩ := hfB k
  obtain ⟨D,hD,hDb⟩ := hgB k
  refine ⟨C+D,add_pos hC hD,?_⟩
  intro p hp x hx
  change ‖iteratedFDeriv ℝ k (f p + g p) x‖ ≤ _
  rw [iteratedFDeriv_add_apply ((hf p).of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))).contDiffAt
    ((hg p).of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hCb p hp x hx) (hDb p hp x hx))

lemma UniformJetBounds.sum {ι : Type*} (s : Finset ι) (f : ι → X → E → ℂ)
    {K : Set X} {B : Set E} (hf : ∀ i ∈ s, ∀ p, ContDiff ℝ ∞ (f i p))
    (hB : ∀ i ∈ s, UniformJetBounds (f i) K B) :
    UniformJetBounds (fun p x => ∑ i ∈ s, f i p x) K B := by
  classical
  intro k
  choose C hC hCb using fun i : s => hB i i.property k
  refine ⟨(∑ i : s, C i)+1,add_pos_of_nonneg_of_pos
    (Finset.sum_nonneg (fun i _ => (hC i).le)) zero_lt_one,?_⟩
  intro p hp x hx
  rw [iteratedFDeriv_fun_sum_apply (fun i hi =>
    ((hf i hi p).of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))).contDiffAt)]
  apply (norm_sum_le _ _).trans
  apply le_trans _ (le_add_of_nonneg_right zero_le_one)
  rw [← Finset.sum_attach]
  exact Finset.sum_le_sum (fun i _ => hCb i p hp x hx)

lemma UniformJetBounds.mul {f g : X → E → ℂ} {K : Set X} {B : Set E}
    (hf : ∀ p, ContDiff ℝ ∞ (f p)) (hg : ∀ p, ContDiff ℝ ∞ (g p))
    (hfB : UniformJetBounds f K B) (hgB : UniformJetBounds g K B) :
    UniformJetBounds (fun p x => f p x * g p x) K B := by
  intro k
  choose C hC hCb using hfB
  choose D hD hDb using hgB
  refine ⟨(∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * C i * D (k-i))+1,
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i).le) (hD (k-i)).le)) zero_lt_one,?_⟩
  intro p hp x hx
  apply (norm_iteratedFDeriv_mul_le (hf p) (hg p) x
    (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))).trans
  apply le_trans _ (le_add_of_nonneg_right zero_le_one)
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (hCb i p hp x hx) (Nat.cast_nonneg _))
    (hDb (k-i) p hp x hx) (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (hC i).le)

lemma UniformJetBounds.common {f : X → E → ℂ} {K : Set X} {B : Set E}
    (h : UniformJetBounds f K B) (m : ℕ) :
    ∃ C ≥ 1, ∀ p ∈ K, ∀ x ∈ B, ∀ k ≤ m, ‖iteratedFDeriv ℝ k (f p) x‖ ≤ C := by
  choose C hC hCb using h
  refine ⟨1+∑ k ∈ Finset.range (m+1), C k,?_,?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => (hC k).le))
  · intro p hp x hx k hk
    apply (hCb k p hp x hx).trans
    have hkB : C k ≤ ∑ i ∈ Finset.range (m+1), C i :=
      Finset.single_le_sum (fun i _ => (hC i).le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    exact hkB.trans (le_add_of_nonneg_left zero_le_one)

end UniformJetBounds

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {X : Type*}

lemma UniformJetBounds.finite_common (f : ℕ → X → E → ℂ) {P : Set X} {B : Set E}
    (h : ∀ j, UniformJetBounds (f j) P B) (J m : ℕ) :
    ∃ C ≥ 1, ∀ j ≤ J, ∀ p ∈ P, ∀ x ∈ B, ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (f j p) x‖ ≤ C := by
  choose C hC hb using fun j => (h j).common m
  refine ⟨1+∑ j ∈ Finset.range (J+1), C j, ?_, ?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => zero_le_one.trans (hC j)))
  · intro j hj p hp x hx k hk
    apply (hb j p hp x hx k hk).trans
    apply le_trans (Finset.single_le_sum (fun i _ => zero_le_one.trans (hC i))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
    exact le_add_of_nonneg_left zero_le_one

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {X : Type*}

lemma norm_iteratedFDeriv_waveDeriv {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (v : E) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (waveDeriv v f) x‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ (k+1) f x‖ := by
  have h : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hb := norm_iteratedFDeriv_clm_apply_const (c := v) (x := x) h.contDiffAt
    (show (k : ℕ∞ω) ≤ ∞ by exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))
  change ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ f y v) x‖ ≤ _
  simpa only [norm_iteratedFDeriv_fderiv] using hb

lemma UniformJetBounds.waveDeriv {f : X → E → ℂ} {P : Set X} {B : Set E}
    (h : UniformJetBounds f P B) (hf : ∀ p, ContDiff ℝ ∞ (f p)) (v : E) :
    UniformJetBounds (fun p => waveDeriv v (f p)) P B := by
  intro k
  obtain ⟨C,hC,hb⟩ := h (k+1)
  refine ⟨1+‖v‖*C, by positivity, ?_⟩
  intro p hp x hx
  apply (norm_iteratedFDeriv_waveDeriv (hf p) v k x).trans
  exact (mul_le_mul_of_nonneg_left (hb p hp x hx) (norm_nonneg _)).trans
    (le_add_of_nonneg_left zero_le_one)

lemma UniformJetBounds.fixed (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (P : Set X) {B : Set E} (hB : IsCompact B) : UniformJetBounds (fun _ => f) P B := by
  intro k
  obtain ⟨C,hC⟩ := hB.exists_bound_of_continuousOn (hf.continuous_iteratedFDeriv
    (show (k : ℕ∞ω) ≤ ∞ by exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))).continuousOn
  exact ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun p hp x hx => (hC x hx).trans (le_max_left _ _)⟩

lemma SmoothJetZero.congr_eventually {f h : E → ℂ} {N : ℕ}
    (hf : SmoothJetZero f N) (he : h =ᶠ[𝓝 0] f) : SmoothJetZero h N := by
  intro k hk
  rw [(he.iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds]
  exact hf k hk

variable {ι : Type*} [Fintype ι]

lemma contDiff_waveGradientPair (e : ι → E) (G : ι → ι → E → ℂ)
    (hG : ∀ i j, ContDiff ℝ ∞ (G i j)) (S V : E → ℂ)
    (hS : ContDiff ℝ ∞ S) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (waveGradientPair e G S V) :=
  ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    ((hG i j).mul (contDiff_waveDeriv (e i) S hS)).mul (contDiff_waveDeriv (e j) V hV)))

lemma contDiff_waveCoordinateOperator (e : ι → E) (G : ι → ι → E → ℂ)
    (b : ι → E → ℂ) (hG : ∀ i j, ContDiff ℝ ∞ (G i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (V : E → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (waveCoordinateOperator e G b V) :=
  (ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    (hG i j).mul (contDiff_waveDeriv (e i) _ (contDiff_waveDeriv (e j) V hV))))).add
      (ContDiff.sum (fun i _ => (hb i).mul (contDiff_waveDeriv (e i) V hV)))

lemma contDiff_finiteWaveTransport (e : ι → E) (G : ι → ι → E → ℂ)
    (b : ι → E → ℂ) (hG : ∀ i j, ContDiff ℝ ∞ (G i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (S V : E → ℂ)
    (hS : ContDiff ℝ ∞ S) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (finiteWaveTransport e G b S V) :=
  ((contDiff_waveGradientPair e G hG V S hV hS).add
    (contDiff_waveGradientPair e G hG S V hS hV)).add
      (((contDiff_waveCoordinateOperator e G b hG hb S hS).add contDiff_const).mul hV)

lemma UniformJetBounds.gradientPair (e : ι → E) (G : X → ι → ι → E → ℂ)
    (hG : ∀ p i j, ContDiff ℝ ∞ (G p i j)) (S V : X → E → ℂ)
    (hS : ∀ p, ContDiff ℝ ∞ (S p)) (hV : ∀ p, ContDiff ℝ ∞ (V p)) {P : Set X} {B : Set E}
    (hGb : ∀ i j, UniformJetBounds (fun p => G p i j) P B)
    (hSb : UniformJetBounds S P B) (hVb : UniformJetBounds V P B) :
    UniformJetBounds (fun p => waveGradientPair e (G p) (S p) (V p)) P B := by
  apply UniformJetBounds.sum
  · intro i hi p
    exact ContDiff.sum (fun j _ => ((hG p i j).mul
      (contDiff_waveDeriv _ _ (hS p))).mul (contDiff_waveDeriv _ _ (hV p)))
  · intro i hi
    apply UniformJetBounds.sum
    · intro j hj p
      exact ((hG p i j).mul (contDiff_waveDeriv _ _ (hS p))).mul (contDiff_waveDeriv _ _ (hV p))
    · intro j hj
      exact ((hGb i j).mul (fun p => hG p i j) (fun p => contDiff_waveDeriv _ _ (hS p))
        (hSb.waveDeriv hS (e i))).mul
        (fun p => (hG p i j).mul (contDiff_waveDeriv _ _ (hS p)))
        (fun p => contDiff_waveDeriv _ _ (hV p)) (hVb.waveDeriv hV (e j))

lemma UniformJetBounds.coordinateOperator (e : ι → E) (G : X → ι → ι → E → ℂ)
    (b : X → ι → E → ℂ) (hG : ∀ p i j, ContDiff ℝ ∞ (G p i j))
    (hb : ∀ p i, ContDiff ℝ ∞ (b p i)) (V : X → E → ℂ)
    (hV : ∀ p, ContDiff ℝ ∞ (V p)) {P : Set X} {B : Set E}
    (hGb : ∀ i j, UniformJetBounds (fun p => G p i j) P B)
    (hbb : ∀ i, UniformJetBounds (fun p => b p i) P B)
    (hVb : UniformJetBounds V P B) :
    UniformJetBounds (fun p => waveCoordinateOperator e (G p) (b p) (V p)) P B := by
  apply UniformJetBounds.add
  · intro p
    exact ContDiff.sum (fun i _ => ContDiff.sum (fun j _ => (hG p i j).mul
      (contDiff_waveDeriv _ _ (contDiff_waveDeriv _ _ (hV p)))))
  · intro p
    exact ContDiff.sum (fun i _ => (hb p i).mul (contDiff_waveDeriv _ _ (hV p)))
  · apply UniformJetBounds.sum
    · intro i hi p
      exact ContDiff.sum (fun j _ => (hG p i j).mul
        (contDiff_waveDeriv _ _ (contDiff_waveDeriv _ _ (hV p))))
    · intro i hi
      apply UniformJetBounds.sum
      · intro j hj p
        exact (hG p i j).mul (contDiff_waveDeriv _ _ (contDiff_waveDeriv _ _ (hV p)))
      · intro j hj
        exact (hGb i j).mul (fun p => hG p i j)
          (fun p => contDiff_waveDeriv _ _ (contDiff_waveDeriv _ _ (hV p)))
          ((hVb.waveDeriv hV (e j)).waveDeriv (fun p => contDiff_waveDeriv _ _ (hV p)) (e i))
  · apply UniformJetBounds.sum
    · intro i hi p
      exact (hb p i).mul (contDiff_waveDeriv _ _ (hV p))
    · intro i hi
      exact (hbb i).mul (fun p => hb p i) (fun p => contDiff_waveDeriv _ _ (hV p)) (hVb.waveDeriv hV (e i))

lemma UniformJetBounds.transport (e : ι → E) (G : X → ι → ι → E → ℂ)
    (b : X → ι → E → ℂ) (hG : ∀ p i j, ContDiff ℝ ∞ (G p i j))
    (hb : ∀ p i, ContDiff ℝ ∞ (b p i)) (S V : X → E → ℂ)
    (hS : ∀ p, ContDiff ℝ ∞ (S p)) (hV : ∀ p, ContDiff ℝ ∞ (V p)) {P : Set X} {B : Set E}
    (hGb : ∀ i j, UniformJetBounds (fun p => G p i j) P B)
    (hbb : ∀ i, UniformJetBounds (fun p => b p i) P B)
    (hSb : UniformJetBounds S P B) (hVb : UniformJetBounds V P B) :
    UniformJetBounds (fun p => finiteWaveTransport e (G p) (b p) (S p) (V p)) P B := by
  have hpair (p) := (contDiff_waveGradientPair e (G p) (hG p) (V p) (S p) (hV p) (hS p)).add
    (contDiff_waveGradientPair e (G p) (hG p) (S p) (V p) (hS p) (hV p))
  have hlap (p) := contDiff_waveCoordinateOperator e (G p) (b p) (hG p) (hb p) (S p) (hS p)
  exact ((UniformJetBounds.gradientPair e G hG V S hV hS hGb hVb hSb).add
    (fun p => contDiff_waveGradientPair e (G p) (hG p) (V p) (S p) (hV p) (hS p))
    (fun p => contDiff_waveGradientPair e (G p) (hG p) (S p) (V p) (hS p) (hV p))
    (UniformJetBounds.gradientPair e G hG S V hS hV hGb hSb hVb)).add hpair
    (fun p => ((hlap p).add contDiff_const).mul (hV p))
    (((UniformJetBounds.coordinateOperator e G b hG hb S hS hGb hbb hSb).add hlap
      (fun _ => contDiff_const) (UniformJetBounds.const 2 P B)).mul
      (fun p => (hlap p).add contDiff_const) hV hVb)
end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

lemma contDiff_smoothWaveEikonal (e : ι → E) (g : ι → ι → E → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (S : E → ℂ) (hS : ContDiff ℝ ∞ S) :
    ContDiff ℝ ∞ (smoothWaveEikonal e g S) :=
  contDiff_const.add (contDiff_waveGradientPair e g hg S S hS hS)

lemma contDiff_smoothWaveRemainder (e : ι → E) (g : ι → ι → E → ℂ) (b : ι → E → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (S : E → ℂ) (V : ℕ → E → ℂ) (hS : ContDiff ℝ ∞ S) (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (j : ℕ) : ContDiff ℝ ∞ (smoothWaveRemainder e g b S V j) := by
  cases j with
  | zero => exact contDiff_finiteWaveTransport e g b hg hb S (V 0) hS (hV 0)
  | succ j =>
    exact (contDiff_finiteWaveTransport e g b hg hb S (V (j+1)) hS (hV (j+1))).add
      (contDiff_waveCoordinateOperator e g b hg hb (V j) (hV j))

lemma smooth_wave_residual_expansion (e : ι → E) (g : ι → ι → E → ℂ) (b : ι → E → ℂ)
    (S : E → ℂ) (V : ℕ → E → ℂ) (hS : ContDiff ℝ ∞ S) (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (J : ℕ) (n : ℝ) (hn : n ≠ 0) :
    (fun x => waveCoordinateOperator e g b (smoothFiniteWave S V J n) x +
      (n : ℂ)*((n : ℂ)+2)*smoothFiniteWave S V J n x) =
    fun x => (n : ℂ)^2 * (∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j *
      (Complex.exp ((n : ℂ)*S x) * (smoothWaveEikonal e g S x * V j x))) +
      (n : ℂ) * (∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j *
        (Complex.exp ((n : ℂ)*S x) * smoothWaveRemainder e g b S V j x)) +
      ((n : ℂ)⁻¹)^J * (Complex.exp ((n : ℂ)*S x) * waveCoordinateOperator e g b (V J) x) := by
  funext x
  have h := finite_wave_residual e g b S hS V hV (smoothWaveRemainder e g b S V)
    rfl (fun j => rfl) (n : ℂ) (by exact_mod_cast hn) J x
  unfold smoothFiniteWave
  rw [h]
  simp only [smoothWaveEikonal, Finset.mul_sum, mul_add]
  apply congrArg₂ (·+·)
  · apply congrArg₂ (·+·)
    · apply Finset.sum_congr rfl
      intro j hj
      ring
    · apply Finset.sum_congr rfl
      intro j hj
      ring
  · ring

lemma waveDeriv_congr_eventually {f h : E → ℂ} {x : E} (he : f =ᶠ[𝓝 x] h) (v : E) :
    waveDeriv v f =ᶠ[𝓝 x] waveDeriv v h := by
  filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (fun L : E →L[ℝ] ℂ => L v) hy

lemma waveGradientPair_congr_eventually (e : ι → E) (g : ι → ι → E → ℂ)
    {S T V W : E → ℂ} {x : E} (hS : S =ᶠ[𝓝 x] T) (hV : V =ᶠ[𝓝 x] W) :
    waveGradientPair e g S V =ᶠ[𝓝 x] waveGradientPair e g T W := by
  have hs : ∀ᶠ y in 𝓝 x, ∀ i, waveDeriv (e i) S y = waveDeriv (e i) T y :=
    eventually_all.mpr (fun i => waveDeriv_congr_eventually hS (e i))
  have hv : ∀ᶠ y in 𝓝 x, ∀ i, waveDeriv (e i) V y = waveDeriv (e i) W y :=
    eventually_all.mpr (fun i => waveDeriv_congr_eventually hV (e i))
  filter_upwards [hs,hv] with y hsy hvy
  simp only [waveGradientPair,hsy,hvy]

lemma waveCoordinateOperator_congr_eventually (e : ι → E) (g : ι → ι → E → ℂ)
    (b : ι → E → ℂ) {V W : E → ℂ} {x : E} (hV : V =ᶠ[𝓝 x] W) :
    waveCoordinateOperator e g b V =ᶠ[𝓝 x] waveCoordinateOperator e g b W := by
  have hv : ∀ᶠ y in 𝓝 x, ∀ i, waveDeriv (e i) V y = waveDeriv (e i) W y :=
    eventually_all.mpr (fun i => waveDeriv_congr_eventually hV (e i))
  have hvv : ∀ᶠ y in 𝓝 x, ∀ i j,
      waveDeriv (e i) (waveDeriv (e j) V) y = waveDeriv (e i) (waveDeriv (e j) W) y :=
    eventually_all.mpr (fun i => eventually_all.mpr (fun j =>
      waveDeriv_congr_eventually (waveDeriv_congr_eventually hV (e j)) (e i)))
  filter_upwards [hv,hvv] with y hvy hvvy
  simp only [waveCoordinateOperator,hvy,hvvy]

lemma finiteWaveTransport_congr_eventually (e : ι → E) (g : ι → ι → E → ℂ)
    (b : ι → E → ℂ) {S T V W : E → ℂ} {x : E}
    (hS : S =ᶠ[𝓝 x] T) (hV : V =ᶠ[𝓝 x] W) :
    finiteWaveTransport e g b S V =ᶠ[𝓝 x] finiteWaveTransport e g b T W := by
  filter_upwards [waveGradientPair_congr_eventually e g hV hS,
    waveGradientPair_congr_eventually e g hS hV,
    waveCoordinateOperator_congr_eventually e g b hS,hV] with y h₁ h₂ h₃ h₄
  simp only [finiteWaveTransport,h₁,h₂,h₃,h₄]

lemma smoothWaveRemainder_congr_eventually (e : ι → E) (g : ι → ι → E → ℂ)
    (b : ι → E → ℂ) (S : E → ℂ) {V W : ℕ → E → ℂ} {x : E}
    (hV : ∀ j, V j =ᶠ[𝓝 x] W j) (j : ℕ) :
    smoothWaveRemainder e g b S V j =ᶠ[𝓝 x] smoothWaveRemainder e g b S W j := by
  cases j with
  | zero => exact finiteWaveTransport_congr_eventually e g b EventuallyEq.rfl (hV 0)
  | succ j =>
    exact (finiteWaveTransport_congr_eventually e g b EventuallyEq.rfl (hV (j+1))).add
      (waveCoordinateOperator_congr_eventually e g b (hV j))
end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {X : Type*}

omit [DecidableEq σ] in
theorem smooth_wave_uniform_residual_bound
    (e : σ → (σ → ℝ)) (g : X → σ → σ → (σ → ℝ) → ℂ) (b : X → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (S : X → (σ → ℝ) → ℂ) (V : X → ℕ → (σ → ℝ) → ℂ)
    (hSsmooth : ∀ p, ContDiff ℝ ∞ (S p)) (hVsmooth : ∀ p j, ContDiff ℝ ∞ (V p j))
    (m D J : ℕ) (hJ : D+m+1 ≤ J) (r c : ℝ) (hr : r ≤ 1) (hc : 0 < c)
    (P : Set X)
    (hS : UniformJetBounds (fun p => S p) P (Metric.ball 0 r))
    (hF : ∀ j, UniformJetBounds (fun p x => smoothWaveEikonal e (g p) (S p) x * V p j x)
      P (Metric.ball 0 r))
    (hR : ∀ j, UniformJetBounds (fun p => smoothWaveRemainder e (g p) (b p) (S p) (V p) j)
      P (Metric.ball 0 r))
    (hL : UniformJetBounds (fun p => waveCoordinateOperator e (g p) (b p) (V p J)) P (Metric.ball 0 r))
    (hFzero : ∀ p ∈ P, ∀ j ≤ J, SmoothJetZero
      (fun x => smoothWaveEikonal e (g p) (S p) x * V p j x) (2*D+3*m+6))
    (hRzero : ∀ p ∈ P, ∀ j ≤ J, SmoothJetZero
      (smoothWaveRemainder e (g p) (b p) (S p) (V p) j) (2*D+3*m+6)) :
    ∃ C > 0, ∀ p ∈ P, ∀ n : ℝ, 1 ≤ n → ∀ x ∈ Metric.ball (0 : σ → ℝ) r,
      ∀ φ : ℝ, n*((S p x).re-φ) ≤ Real.sqrt n*‖x‖-c*n*‖x‖^2 →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k (fun y =>
        waveCoordinateOperator e (g p) (b p) (smoothFiniteWave (S p) (V p) J n) y +
         (n : ℂ)*((n : ℂ)+2)*smoothFiniteWave (S p) (V p) J n y) x‖ ≤
        C*(n^(D+1))⁻¹*Real.exp (n*φ) := by
  obtain ⟨CS,hCS,hSb⟩ := hS.common m
  obtain ⟨CF,hCF,hFb⟩ := UniformJetBounds.finite_common _ hF J (2*D+3*m+6)
  obtain ⟨CR,hCR,hRb⟩ := UniformJetBounds.finite_common _ hR J (2*D+3*m+6)
  obtain ⟨CL,hCL,hLb⟩ := hL.common m
  let A := max CF (max CR CL)
  have hFA : CF ≤ A := le_max_left _ _
  have hRA : CR ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hLA : CL ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hA : 0 ≤ A := zero_le_one.trans (hCF.trans hFA)
  let Ck := fun k => 2*(J+1 : ℕ) *
      (expJetConstant k CS*A*((2*(k+(D+3))).factorial : ℝ)*Real.exp c⁻¹) +
        expJetConstant k CS*A*Real.exp c⁻¹
  have hCk (k : ℕ) : 0 ≤ Ck k := by
    dsimp [Ck]
    have he := expJetConstant_nonneg k (zero_le_one.trans hCS)
    positivity
  let C := 1+∑ k ∈ Finset.range (m+1), Ck k
  have hC : 0 < C := by
    dsimp [C]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun k _ => hCk k))
  refine ⟨C,hC,?_⟩
  intro p hp n hn x hx φ hphase k hk
  have hCkC : Ck k ≤ C := (Finset.single_le_sum (fun i _ => hCk i)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).trans (le_add_of_nonneg_left zero_le_one)
  have horder : 2*D+3*k+6 ≤ 2*D+3*m+6 := by omega
  have hbound := finite_scheduled_residual_bound (S p)
    (fun j x => smoothWaveEikonal e (g p) (S p) x * V p j x)
    (smoothWaveRemainder e (g p) (b p) (S p) (V p))
    (waveCoordinateOperator e (g p) (b p) (V p J))
    (hSsmooth p) (fun j => (contDiff_smoothWaveEikonal e _ (hg p) _ (hSsmooth p)).mul (hVsmooth p j))
    (contDiff_smoothWaveRemainder e _ _ (hg p) (hb p) _ _ (hSsmooth p) (hVsmooth p))
    (contDiff_waveCoordinateOperator e _ _ (hg p) (hb p) _ (hVsmooth p J))
    k D J (by omega) x CS A n φ c r hCS hA hn hc hr hx
    (fun i hi hik => hSb p hp x hx i (hik.trans hk))
    (fun j hj => (hFzero p hp j hj).mono horder)
    (fun j hj => (hRzero p hp j hj).mono horder)
    (fun j hj y hy => (hFb j hj p hp y hy _ horder).trans hFA)
    (fun j hj y hy => (hRb j hj p hp y hy _ horder).trans hRA)
    (fun i hi => (hLb p hp x hx i (hi.trans hk)).trans hLA) hphase
  rw [smooth_wave_residual_expansion e _ _ _ _ (hSsmooth p) (hVsmooth p) _ n (ne_of_gt (zero_lt_one.trans_le hn))]
  apply hbound.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCkC (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hn) _)))
    (Real.exp_pos _).le

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {X : Type*}

lemma smoothWaveEikonal_realPolyEval (g : σ → σ → (σ → ℝ) → ℂ) (S : MvPolynomial σ ℂ) :
    smoothWaveEikonal (fun i => Pi.single i 1) g (realPolyEval S) = smoothEikonalResidual g S :=
  (smoothEikonalResidual_eq_gradientPair g S).symm

lemma smoothWaveRemainder_realPolyEval (g : σ → σ → (σ → ℝ) → ℂ) (b : σ → (σ → ℝ) → ℂ)
    (S : MvPolynomial σ ℂ) (V : ℕ → MvPolynomial σ ℂ) (j : ℕ) :
    smoothWaveRemainder (fun i => Pi.single i 1) g b (realPolyEval S) (fun j => realPolyEval (V j)) j =
      polynomialWaveRemainder g b S V j := by
  cases j with
  | zero => exact (smoothWaveTransport_eq_finite g b S (V 0)).symm
  | succ j =>
    simp only [smoothWaveRemainder,polynomialWaveRemainder,
      smoothWaveTransport_eq_finite,smoothPolynomialLaplacian_eq_operator]

lemma cutoff_polynomial_remainders_vanish
    (g : σ → σ → (σ → ℝ) → ℂ) (b : σ → (σ → ℝ) → ℂ)
    (S : MvPolynomial σ ℂ) (V : ℕ → MvPolynomial σ ℂ)
    (ζ : (σ → ℝ) → ℂ) (hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (K : ℕ)
    (hF : ∀ j, SmoothJetZero (fun x => smoothEikonalResidual g S x * realPolyEval (V j) x) K)
    (J : ℕ) (hR : ∀ j ≤ J, SmoothJetZero (polynomialWaveRemainder g b S V j) K) :
    (∀ j, SmoothJetZero (fun x => smoothWaveEikonal (fun i => Pi.single i 1) g (realPolyEval S) x *
      (ζ x * realPolyEval (V j) x)) K) ∧
    (∀ j ≤ J, SmoothJetZero (smoothWaveRemainder (fun i => Pi.single i 1) g b (realPolyEval S)
      (fun j x => ζ x * realPolyEval (V j) x) j) K) := by
  have hV (j) : (fun x => ζ x * realPolyEval (V j) x) =ᶠ[𝓝 0] realPolyEval (V j) := by
    filter_upwards [hζ] with x hx
    simp only [hx,one_mul]
  constructor
  · intro j
    apply (hF j).congr_eventually
    rw [smoothWaveEikonal_realPolyEval]
    exact EventuallyEq.rfl.mul (hV j)
  · intro j hj
    apply (hR j hj).congr_eventually
    rw [← smoothWaveRemainder_realPolyEval]
    exact smoothWaveRemainder_congr_eventually _ _ _ _ hV j

omit [DecidableEq σ] in
lemma uniformJetBounds_smoothWaveEikonal
    (e : σ → (σ → ℝ)) (g : X → σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (S : X → (σ → ℝ) → ℂ)
    (hS : ∀ p, ContDiff ℝ ∞ (S p)) {P : Set X} {B : Set (σ → ℝ)}
    (hgB : ∀ i j, UniformJetBounds (fun p => g p i j) P B)
    (hSB : UniformJetBounds S P B) :
    UniformJetBounds (fun p => smoothWaveEikonal e (g p) (S p)) P B :=
  (UniformJetBounds.const 1 P B).add (fun _ => contDiff_const)
    (fun p => contDiff_waveGradientPair e (g p) (hg p) (S p) (S p) (hS p) (hS p))
    (UniformJetBounds.gradientPair e g hg S S hS hS hgB hSB hSB)

omit [DecidableEq σ] in
lemma uniformJetBounds_smoothWaveRemainder
    (e : σ → (σ → ℝ)) (g : X → σ → σ → (σ → ℝ) → ℂ) (b : X → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (S : X → (σ → ℝ) → ℂ) (V : X → ℕ → (σ → ℝ) → ℂ)
    (hS : ∀ p, ContDiff ℝ ∞ (S p)) (hV : ∀ p j, ContDiff ℝ ∞ (V p j))
    {P : Set X} {B : Set (σ → ℝ)}
    (hgB : ∀ i j, UniformJetBounds (fun p => g p i j) P B)
    (hbB : ∀ i, UniformJetBounds (fun p => b p i) P B)
    (hSB : UniformJetBounds S P B) (hVB : ∀ j, UniformJetBounds (fun p => V p j) P B) (j : ℕ) :
    UniformJetBounds (fun p => smoothWaveRemainder e (g p) (b p) (S p) (V p) j) P B := by
  cases j with
  | zero =>
    exact UniformJetBounds.transport e g b hg hb S (fun p => V p 0) hS
      (fun p => hV p 0) hgB hbB hSB (hVB 0)
  | succ j =>
    exact (UniformJetBounds.transport e g b hg hb S (fun p => V p (j+1)) hS
      (fun p => hV p (j+1)) hgB hbB hSB (hVB (j+1))).add
      (fun p => contDiff_finiteWaveTransport e (g p) (b p) (hg p) (hb p) (S p) (V p (j+1)) (hS p) (hV p (j+1)))
      (fun p => contDiff_waveCoordinateOperator e (g p) (b p) (hg p) (hb p) (V p j) (hV p j))
      (UniformJetBounds.coordinateOperator e g b hg hb (fun p => V p j) (fun p => hV p j) hgB hbB (hVB j))

theorem cutoff_polynomial_wave_residual_bound_oai
    (g : X → σ → σ → (σ → ℝ) → ℂ) (b : X → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (S : X → MvPolynomial σ ℂ) (V : X → ℕ → MvPolynomial σ ℂ)
    (ζ : (σ → ℝ) → ℂ) (hζ : ContDiff ℝ ∞ ζ) (hζ₀ : ζ =ᶠ[𝓝 0] fun _ => 1)
    (m D J : ℕ) (hJ : D+m+1 ≤ J) (r c : ℝ) (hr : r ≤ 1) (hc : 0 < c)
    (P : Set X)
    (hgB : ∀ i j, UniformJetBounds (fun p => g p i j) P (Metric.ball 0 r))
    (hbB : ∀ i, UniformJetBounds (fun p => b p i) P (Metric.ball 0 r))
    (hSB : UniformJetBounds (fun p => realPolyEval (S p)) P (Metric.ball 0 r))
    (hVB : ∀ j, UniformJetBounds (fun p => realPolyEval (V p j)) P (Metric.ball 0 r))
    (hFzero : ∀ p ∈ P, ∀ j, SmoothJetZero
      (fun x => smoothEikonalResidual (g p) (S p) x * realPolyEval (V p j) x) (2*D+3*m+6))
    (hRzero : ∀ p ∈ P, ∀ j ≤ J, SmoothJetZero
      (polynomialWaveRemainder (g p) (b p) (S p) (V p) j) (2*D+3*m+6)) :
    ∃ C > 0, ∀ p ∈ P, ∀ n : ℝ, 1 ≤ n → ∀ x ∈ Metric.ball (0 : σ → ℝ) r,
      ∀ φ : ℝ, n*((realPolyEval (S p) x).re-φ) ≤ Real.sqrt n*‖x‖-c*n*‖x‖^2 →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k (fun y =>
        waveCoordinateOperator (fun i => Pi.single i 1) (g p) (b p)
          (smoothFiniteWave (realPolyEval (S p)) (fun j x => ζ x * realPolyEval (V p j) x) J n) y +
         (n : ℂ)*((n : ℂ)+2)*smoothFiniteWave (realPolyEval (S p))
          (fun j x => ζ x * realPolyEval (V p j) x) J n y) x‖ ≤
        C*(n^(D+1))⁻¹*Real.exp (n*φ) := by
  let W := fun p j x => ζ x * realPolyEval (V p j) x
  have hW (p j) : ContDiff ℝ ∞ (W p j) := hζ.mul (contDiff_realPolyEval _)
  have hζB : UniformJetBounds (fun _ : X => ζ) P (Metric.ball 0 r) :=
    (UniformJetBounds.fixed ζ hζ P (isCompact_closedBall 0 r)).mono subset_rfl Metric.ball_subset_closedBall
  have hWB (j) : UniformJetBounds (fun p => W p j) P (Metric.ball 0 r) :=
    hζB.mul (fun _ => hζ) (fun _ => contDiff_realPolyEval _) (hVB j)
  have hE := uniformJetBounds_smoothWaveEikonal (fun i => Pi.single i 1) g hg
    (fun p => realPolyEval (S p)) (fun _ => contDiff_realPolyEval _) hgB hSB
  apply smooth_wave_uniform_residual_bound (fun i => Pi.single i 1) g b hg hb
    (fun p => realPolyEval (S p)) W (fun _ => contDiff_realPolyEval _) hW m D J hJ r c hr hc P hSB
  · intro j
    exact hE.mul (fun p => contDiff_smoothWaveEikonal _ _ (hg p) _ (contDiff_realPolyEval _))
      (fun p => hW p j) (hWB j)
  · exact uniformJetBounds_smoothWaveRemainder _ g b hg hb _ W (fun _ => contDiff_realPolyEval _) hW hgB hbB hSB hWB
  · exact UniformJetBounds.coordinateOperator _ g b hg hb (fun p => W p J) (fun p => hW p J) hgB hbB (hWB J)
  · intro p hp j hj
    exact (cutoff_polynomial_remainders_vanish (g p) (b p) (S p) (V p) ζ hζ₀ _
      (hFzero p hp) J (hRzero p hp)).1 j
  · intro p hp j hj
    exact (cutoff_polynomial_remainders_vanish (g p) (b p) (S p) (V p) ζ hζ₀ _
      (hFzero p hp) J (hRzero p hp)).2 j hj
end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.YauCounterexamples.cutoff_polynomial_wave_residual_bound_oai.{u_1, u_2} := @OAI.YauCounterexamples.cutoff_polynomial_wave_residual_bound_oai.{u_1, u_2}
