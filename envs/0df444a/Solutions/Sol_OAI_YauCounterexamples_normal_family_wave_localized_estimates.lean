-- Prove2me | solution 1 for OAI.YauCounterexamples.normal_family_wave_localized_estimates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:21:49.825804+00:00
-- url     : https://prove2.me/submissions/9a5d9215-0bd3-40c9-8e9a-79a00951b920

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_admissible_cutoff_wave_residual
import Theorems.Thm_OAI_YauCounterexamples_all_admissible_generated_gaussian
import Theorems.Thm_OAI_YauCounterexamples_generated_wave_uniform_jets

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_HessianJet
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

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
section SecondJetBridge
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma hessianFromJet_iterated (f : E → F) (x : E) :
    hessianFromJet (iteratedFDeriv ℝ 2 f x) = fderiv ℝ (fderiv ℝ f) x := by
  ext v w
  change (iteratedFDeriv ℝ 2 f x) (Fin.cons v (fun _ => w)) = _
  simpa using iteratedFDeriv_two_apply (𝕜 := ℝ) f x (Fin.cons v (fun _ => w))

lemma continuous_hessian_of_iterated {X : Type*} [TopologicalSpace X]
    (f : X → E → F)
    (hf : Continuous (fun q : X × E => iteratedFDeriv ℝ 2 (f q.1) q.2)) :
    Continuous (fun q : X × E => fderiv ℝ (fderiv ℝ (f q.1)) q.2) := by
  simpa only [Function.comp_def, hessianFromJet_iterated] using hessianFromJet.continuous.comp hf

end SecondJetBridge



end YauCounterexamples
end

end OAI
end

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RealPhaseLinear
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

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
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι]

lemma phase_vector_ne_zero (z : ι → ℂ) (hz : ∑ i, z i*z i = -1) : z ≠ 0 := by
  intro he
  simp [he] at hz

lemma phase_matrix_annihilation (Q : Matrix ι ι ℂ) (z : ι → ℂ)
    (h : Q *ᵥ z = 0) (k : ι) : ∑ i, z i * Q k i = 0 := by
  simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply, mul_comm] using congrFun h k



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_ClosedPhaseMatrixValid
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
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {X : Type*} [TopologicalSpace X]

lemma isClosed_phaseMatrixValid (H : X → RealForm PhaseSpace) (z : X → Fin 3 → ℂ)
    (hH : Continuous (fun x => phaseFormMatrix (H x))) (hz : Continuous z)
    (κ C : ℝ) :
    IsClosed {p : X × ComplexPhaseMatrix | PhaseMatrixValid (H p.1) (z p.1) κ C p.2} := by
  have hs : IsClosed {p : X × ComplexPhaseMatrix | p.2ᵀ = p.2} :=
    isClosed_eq (by fun_prop) continuous_snd
  have ha : IsClosed {p : X × ComplexPhaseMatrix | p.2 *ᵥ z p.1 = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  have hb : IsClosed {p : X × ComplexPhaseMatrix | ‖p.2‖ ≤ C} :=
    isClosed_le continuous_snd.norm continuous_const
  have hg : IsClosed {p : X × ComplexPhaseMatrix | ∀ v,
      4*κ*squareSum v ≤ realQuadratic (phaseFormMatrix (H p.1)-p.2.map Complex.re) v} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro v
    apply isClosed_le continuous_const
    unfold realQuadratic
    have hM : Continuous (fun p : X × ComplexPhaseMatrix => phaseFormMatrix (H p.1)) :=
      hH.comp continuous_fst
    fun_prop
  exact hs.inter (ha.inter (hb.inter hg))

theorem boundedPhaseSet_isCompact [CompactSpace X]
    (H : X → RealForm PhaseSpace) (hH : Continuous (fun x => phaseFormMatrix (H x)))
    (B κ C : ℝ) : IsCompact (boundedPhaseSet H B κ C) := by
  have hz : IsClosed {p : ((X × (Fin 3 → ℂ)) × ComplexPhaseMatrix) | ‖p.1.2‖ ≤ B} :=
    isClosed_le (continuous_snd.comp continuous_fst).norm continuous_const
  have hn : IsClosed {p : ((X × (Fin 3 → ℂ)) × ComplexPhaseMatrix) |
      ∑ i, p.1.2 i * p.1.2 i = -1} := isClosed_eq (by fun_prop) continuous_const
  have hv := isClosed_phaseMatrixValid (fun p : X × (Fin 3 → ℂ) => H p.1)
    (fun p => p.2) (hH.comp continuous_fst) continuous_snd κ C
  have hclosed : IsClosed (boundedPhaseSet H B κ C) := hz.inter (hn.inter hv)
  apply ((isCompact_univ.prod (isCompact_closedBall (0 : Fin 3 → ℂ) B)).prod
    (isCompact_closedBall (0 : ComplexPhaseMatrix) C)).of_isClosed_subset hclosed
  intro p hp
  exact ⟨⟨mem_univ _, by simpa only [Metric.mem_closedBall, dist_zero_right] using hp.1⟩,
    by simpa only [Metric.mem_closedBall, dist_zero_right] using hp.2.2.2.2.1⟩

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ActualHessianForm
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
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix MvPolynomial
open scoped Topology ContDiff Matrix Matrix.Norms.Elementwise
namespace YauCounterexamples

lemma continuous_actualHessianForm {X : Type*} [TopologicalSpace X]
    (φ : X → PhaseSpace → ℝ)
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2)) :
    Continuous (fun p => phaseFormMatrix (actualHessianForm (φ p))) := by
  have hH := (continuous_hessian_of_iterated φ hφ2).comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : X => (0 : PhaseSpace))))
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (hH.clm_apply continuous_const).clm_apply continuous_const

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_GaussianLinearDistortion
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
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
namespace YauCounterexamples

lemma gaussian_linear_distortion {κ A t : ℝ} (hκ : 0 < κ) :
    A*t-κ*t^2 ≤ t-κ/2*t^2 + (A-1)^2/(2*κ) := by
  have hc : 2*κ*((A-1)^2/(2*κ)) = (A-1)^2 := by field_simp
  nlinarith [sq_nonneg (κ*t-(A-1))]

lemma gaussian_phase_coordinate_shift {n κ A q s φ : ℝ}
    (hn : 0 < n) (hκ : 0 < κ)
    (hphase : n*(s-φ) ≤ A*Real.sqrt n*q-κ*n*q^2) :
    n*(s-(φ+(A-1)^2/(2*κ)/n)) ≤
      Real.sqrt n*q-(κ/2)*n*q^2 := by
  have hs := gaussian_linear_distortion (A := A) (t := Real.sqrt n*q) hκ
  rw [mul_pow,Real.sq_sqrt hn.le] at hs
  have he : n*((A-1)^2/(2*κ)/n) = (A-1)^2/(2*κ) := by field_simp
  nlinarith

lemma gaussian_phase_shift_exp {n κ A φ : ℝ} (hn : n ≠ 0) :
    Real.exp (n*(φ+(A-1)^2/(2*κ)/n)) =
      Real.exp ((A-1)^2/(2*κ))*Real.exp (n*φ) := by
  have he : n*(φ+(A-1)^2/(2*κ)/n) = (A-1)^2/(2*κ)+n*φ := by field_simp; ring
  rw [he,Real.exp_add]
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

variable [TopologicalSpace X]
lemma uniformJetBounds_of_continuous_jets (f : X → E → ℂ)
    (hf : ∀ k, Continuous (fun q : X × E => iteratedFDeriv ℝ k (f q.1) q.2))
    {K : Set X} (hK : IsCompact K) {B : Set E} (hB : IsCompact B) :
    UniformJetBounds f K B := by
  intro k
  obtain ⟨C,hC⟩ := (hK.prod hB).exists_bound_of_continuousOn (hf k).continuousOn
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  exact fun p hp x hx => (hC (p,x) ⟨hp,hx⟩).trans (le_max_left _ _)
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : Type*}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma smoothFiniteWave_eq_sum (S : E → ℂ) (V : ℕ → E → ℂ) (J : ℕ) (n : ℝ) :
    smoothFiniteWave S V J n = fun x => ∑ j ∈ Finset.range (J+1),
      ((n : ℂ)⁻¹)^j * (Complex.exp ((n : ℂ)*S x)*V j x) := by
  funext x
  simp only [smoothFiniteWave,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem smooth_finite_wave_uniform_derivatives (S : X → E → ℂ) (V : X → ℕ → E → ℂ)
    (hS : ∀ p, ContDiff ℝ ∞ (S p)) (hV : ∀ p j, ContDiff ℝ ∞ (V p j))
    (m J : ℕ) {P : Set X} {B : Set E}
    (hSB : UniformJetBounds S P B) (hVB : ∀ j, UniformJetBounds (fun p => V p j) P B)
    (c : ℝ) (hc : 0 < c) :
    ∃ C > 0, ∀ p ∈ P, ∀ n : ℝ, 1 ≤ n → ∀ x ∈ B, ∀ φ : ℝ,
      n*((S p x).re-φ) ≤ Real.sqrt n*‖x‖-c*n*‖x‖^2 → ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (smoothFiniteWave (S p) (V p) J n) x‖ ≤ C*n^k*Real.exp (n*φ) := by
  obtain ⟨CS,hCS,hSb⟩ := hSB.common m
  obtain ⟨CV,hCV,hVb⟩ := UniformJetBounds.finite_common _ hVB J m
  let Ck := fun k => (J+1 : ℕ)*expJetConstant k CS*CV*Real.exp c⁻¹
  have hCk (k) : 0 ≤ Ck k := by
    dsimp [Ck]
    have he := expJetConstant_nonneg k (zero_le_one.trans hCS)
    positivity
  let C := 1+∑ k ∈ Finset.range (m+1), Ck k
  have hC : 0 < C := by
    dsimp [C]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun k _ => hCk k)
  refine ⟨C,hC,?_⟩
  intro p hp n hn x hx φ hphase k hk
  have hCkC : Ck k ≤ C := (Finset.single_le_sum (fun i _ => hCk i)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).trans (le_add_of_nonneg_left zero_le_one)
  have he : ∀ j, ContDiff ℝ ∞ (fun y => Complex.exp ((n : ℂ)*S p y)*V p j y) := fun j =>
    (Complex.contDiff_exp.comp (contDiff_const.mul (hS p))).mul (hV p j)
  have hec := expJetConstant_nonneg k (zero_le_one.trans hCS)
  rw [smoothFiniteWave_eq_sum]
  apply (norm_iteratedFDeriv_weighted_sum _ he J k x _ (inverse_frequency_norm_le_one hn)
    (expJetConstant k CS*CV*Real.exp c⁻¹*n^k*Real.exp (n*φ)) (by positivity)
    (fun j hj => bounded_wave_term (S p) (V p j) (hS p) (hV p j) k x CS CV n φ c hCS
      (zero_le_one.trans hCV) hn hc
      (fun i hi hik => hSb p hp x hx i (hik.trans hk))
      (fun i hi => hVb j hj p hp x hx i (hi.trans hk)) hphase)).trans
  calc
    _ = Ck k*n^k*Real.exp (n*φ) := by dsimp [Ck]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCkC (pow_nonneg (zero_le_one.trans hn) _)) (Real.exp_pos _).le

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_CanonicalCutoffWave
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

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
open scoped Topology
open Set Filter Matrix MvPolynomial
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma norm_pi_le_euclidean (x : Fin 3 → ℝ) : ‖x‖ ≤ ‖(WithLp.toLp 2 x : PhaseSpace)‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    (fun i => PiLp.norm_apply_le (WithLp.toLp 2 x : PhaseSpace) i)


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PulledGradient
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma selfMetricFlat_invertible (g : SmoothMetric E E) (x : E) :
    (selfMetricFlat g x).IsInvertible := by
  rw [←localMetricFlat_self g x x]
  exact localMetricFlat_invertible g x x (mem_baseSet_trivializationAt E _ x)

attribute [local instance] OAI.YauCounterexamples.metricDualNorm
attribute [local instance] OAI.YauCounterexamples.metricDualSpace
attribute [local instance] OAI.YauCounterexamples.metricFormNorm
attribute [local instance] OAI.YauCounterexamples.metricFormSpace
attribute [local instance] OAI.YauCounterexamples.metricTriNorm
attribute [local instance] OAI.YauCounterexamples.metricTriSpace
lemma contDiff_metricChristoffel (g : SmoothMetric E E) : ContDiff ℝ ∞ (metricChristoffel g) := by
  have hG := contDiff_selfMetricFlat g
  have hGi : ContDiff ℝ ∞ (fun x => (selfMetricFlat g x).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (selfMetricFlat_invertible g x).contDiffAt_map_inverse.comp x hG.contDiffAt
  have hD := hG.fderiv_right (m := ∞) (by simp)
  have hDf : ContDiff ℝ ∞ (fun x => (fderiv ℝ (selfMetricFlat g) x).flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearMap.contDiff.comp hD
  have hK : ContDiff ℝ ∞ (fun x => coordinateKoszul (fderiv ℝ (selfMetricFlat g) x)) :=
    (hD.add hDf |>.sub (contDiff_const.clm_comp hDf)).const_smul (1/2 : ℝ)
  exact (contDiff_const.clm_apply hGi).clm_comp hK

lemma compact_selfMetricFlat_lower (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, ∀ v : E, m*‖v‖^2 ≤ selfMetricFlat g x v v :=
  compact_positive_bilinear_lower hK (selfMetricFlat g) (contDiff_selfMetricFlat g).continuous
    (fun x _ _ hv => selfMetricFlat_pos g x hv)


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff
open scoped InnerProductSpace



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_FrameDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance frameDualNorm_r99e628_1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
attribute [local instance] OAI.YauCounterexamples.frameDualSpace
local instance frameFormNorm_r99e628_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance frameFormSpace_r99e628_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
omit [FiniteDimensional ℝ E] in
lemma metricFrameSet_isClosed (g : SmoothMetric E E) {K : Set E} (hK : IsClosed K) :
    IsClosed (metricFrameSet g K) := by
  apply (hK.preimage continuous_fst).inter
  change IsClosed {q : E × (E →L[ℝ] E) | ∀ v w : E,
    selfMetricFlat g q.1 (q.2 v) (q.2 w) = inner ℝ v w}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro v
  apply isClosed_iInter
  intro w
  exact isClosed_eq
    (((contDiff_selfMetricFlat g).continuous.comp continuous_fst).clm_apply
      (continuous_snd.clm_apply continuous_const) |>.clm_apply
      (continuous_snd.clm_apply continuous_const)) continuous_const

lemma metricFrameSet_bound (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    ∃ R > 0, ∀ q ∈ metricFrameSet g K, ‖q.2‖ ≤ R := by
  obtain ⟨m,hm,hml⟩ := compact_selfMetricFlat_lower g hK
  refine ⟨(Real.sqrt m)⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr hm), ?_⟩
  intro q hq
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  intro v
  have hlow := hml q.1 hq.1 (q.2 v)
  rw [hq.2 v v, real_inner_self_eq_norm_sq] at hlow
  have hh : Real.sqrt m * ‖q.2 v‖ ≤ ‖v‖ :=
    le_of_sq_le_sq (by simpa only [mul_pow,Real.sq_sqrt hm.le] using hlow) (norm_nonneg _)
  rw [← div_eq_inv_mul, le_div_iff₀ (Real.sqrt_pos.mpr hm)]
  rwa [mul_comm]

theorem metricFrameSet_isCompact (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    IsCompact (metricFrameSet g K) := by
  obtain ⟨R,hR,hb⟩ := metricFrameSet_bound g hK
  apply (hK.prod (isCompact_closedBall (0 : E →L[ℝ] E) R)).of_isClosed_subset
    (metricFrameSet_isClosed g hK.isClosed)
  intro q hq
  exact ⟨hq.1, by simpa only [Metric.mem_closedBall, dist_zero_right] using hb q hq⟩

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContDiffSmoothFiniteWave
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.coordinateRegionMeasure_finite _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
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
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.normalFamilyVecNorm
attribute [local instance] OAI.YauCounterexamples.normalFamilyVecSpace
attribute [local instance] OAI.YauCounterexamples.normalFamilyBiVecNorm
attribute [local instance] OAI.YauCounterexamples.normalFamilyBiVecSpace
attribute [local instance] OAI.YauCounterexamples.normalFamilyDualNorm
attribute [local instance] OAI.YauCounterexamples.normalFamilyDualSpace
local instance normalFamilyFormNorm_r99e628_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance normalFamilyFormSpace_r99e628_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
lemma contDiff_frameChristoffel (g : SmoothMetric E E) :
    ContDiff ℝ ∞ (fun q : E × (E →L[ℝ] E) =>
      (metricChristoffel g q.1).bilinearComp q.2 q.2) := by
  have h1 : ContDiff ℝ ∞ (fun q : E × (E →L[ℝ] E) => (metricChristoffel g q.1).comp q.2) :=
    ((contDiff_metricChristoffel g).comp contDiff_fst).clm_comp contDiff_snd
  have h2 := (ContinuousLinearMap.flipₗᵢ ℝ E E E).toContinuousLinearMap.contDiff.comp h1
  have h3 := h2.clm_comp contDiff_snd
  exact (ContinuousLinearMap.flipₗᵢ ℝ E E E).toContinuousLinearMap.contDiff.comp h3

lemma contDiff_normalJetFamily (g : SmoothMetric E E) :
    ContDiff ℝ ∞ (fun q : (E × (E →L[ℝ] E)) × E =>
      normalJetMap q.1.1 q.1.2 ((metricChristoffel g q.1.1).bilinearComp q.1.2 q.1.2) q.2) := by
  have hC : ContDiff ℝ ∞ (fun q : (E × (E →L[ℝ] E)) × E => (metricChristoffel g q.1.1).bilinearComp q.1.2 q.1.2) :=
    (contDiff_frameChristoffel g).comp contDiff_fst
  exact (contDiff_fst.fst.add (contDiff_fst.snd.clm_apply contDiff_snd)).sub
    ((hC.clm_apply contDiff_snd |>.clm_apply contDiff_snd).const_smul (1/2 : ℝ))

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
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {P E F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
lemma normal_iteratedFDeriv_comp_clm_at (L : F →L[ℝ] E) {f : E → G} {x : F} (n : ℕ)
    (hf : ContDiffAt ℝ n f (L x)) :
    iteratedFDeriv ℝ n (f ∘ L) x =
      (iteratedFDeriv ℝ n f (L x)).compContinuousLinearMap (fun _ => L) := by
  obtain ⟨U,hU,hu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨V,hVU,hVo,hx⟩ := mem_nhds_iff.mp hU
  have he := L.iteratedFDerivWithin_comp_right (hu.mono hVU) hVo.uniqueDiffOn
    (hVo.preimage L.continuous).uniqueDiffOn hx (le_refl (n : WithTop ℕ∞))
  rw [iteratedFDerivWithin_of_isOpen n hVo hx,
    iteratedFDerivWithin_of_isOpen n (hVo.preimage L.continuous) hx] at he
  exact he

lemma parameter_iteratedFDeriv (f : P × E → F) (t : P) (x : E) (n : ℕ)
    (hf : ContDiffAt ℝ n f (t,x)) :
    iteratedFDeriv ℝ n (fun y => f (t,y)) x =
      (iteratedFDeriv ℝ n f (t,x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ P E) := by
  let L := ContinuousLinearMap.inr ℝ P E
  let q : P × E → F := fun z => f ((t,0)+z)
  have hq : ContDiffAt ℝ n q (L x) := by
    have hg : ContDiffAt ℝ n (fun z : P × E => (t,0)+z) (L x) := by fun_prop
    exact (show ContDiffAt ℝ n f ((t,0)+L x) by simpa [L] using hf).comp (L x) hg
  have hj := normal_iteratedFDeriv_comp_clm_at L n hq
  simpa [q,L,Function.comp_def,iteratedFDeriv_comp_add_left] using hj

lemma continuousAt_parameter_iteratedFDeriv (f : P × E → F) {z : P × E} (n : ℕ)
    (hf : ContDiffAt ℝ ∞ f z) :
    ContinuousAt (fun w : P × E => iteratedFDeriv ℝ n (fun y => f (w.1,y)) w.2) z := by
  have hc := (ContinuousMultilinearMap.continuous_precomp
    (fun _ : Fin n => ContinuousLinearMap.inr ℝ P E)).continuousAt.comp
      (hf.continuousAt_iteratedFDeriv (k := n) (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))
  apply hc.congr_of_eventuallyEq
  filter_upwards [(hf.of_le (show (n : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) from ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).eventually (by simp)] with w hw
  exact parameter_iteratedFDeriv f w.1 w.2 n hw


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
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
section ParameterDerivative
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma continuous_parameter_iteratedFDeriv (f : P × E → F) (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    Continuous (fun q : P × E => iteratedFDeriv ℝ k (fun x => f (q.1,x)) q.2) :=
  continuous_iff_continuousAt.mpr (fun _ => continuousAt_parameter_iteratedFDeriv f k hf.contDiffAt)
end ParameterDerivative

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
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma normal_profile_family_smooth (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun q : NormalWaveParameter × NormalWaveSpace =>
      φ (normalJetMap q.1.1 q.1.2 ((metricChristoffel g q.1.1).bilinearComp q.1.2 q.1.2) q.2)) :=
  hφ.comp (contDiff_normalJetFamily g)


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
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_AdmissibleCutoffWaveLocalizedDerivatives
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.coordinateRegionMeasure_finite _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
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
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix MvPolynomial
open scoped Topology ContDiff Matrix.Norms.Elementwise
section
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {X : Type*}
theorem generated_cutoff_wave_derivative_estimate [TopologicalSpace X]
    (g : X → σ → σ → (σ → ℝ) → ℂ) (b : X → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (σ → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (σ → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
    (s : X → ℂ) (hs : Continuous s) (z : X → σ → ℂ) (hz : ∀ i, Continuous (fun p => z p i))
    (hz₀ : ∀ p, z p ≠ 0) (Q : X → σ → σ → ℂ)
    (hQ : ∀ i j, Continuous (fun p => Q p i j)) (hsym : ∀ p i j, Q p i j = Q p j i)
    (hnull : ∀ p, ∑ i, z p i*z p i = -1) (hQz : ∀ p k, ∑ i, z p i*Q p k i = 0)
    (ζ : (σ → ℝ) → ℂ) (hζ : ContDiff ℝ ∞ ζ) (_hζ₀ : ζ =ᶠ[𝓝 0] fun _ => 1)
    (m D : ℕ) (r c : ℝ) (_hr : r ≤ 1) (hc : 0 < c)
    {P : Set X} (hP : IsCompact P) :
    let K := 2*D+3*m+6
    let J := D+m+1
    let S := fun p => smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1)
    let V := fun p => uniformSmoothWaveAmplitudes (g p) (b p) (S p) (z p) K J
    ∃ C > 0, ∀ p ∈ P, ∀ n : ℝ, 1 ≤ n → ∀ x ∈ Metric.ball (0 : σ → ℝ) r,
      ∀ φ : ℝ, n*((realPolyEval (S p) x).re-φ) ≤ Real.sqrt n*‖x‖-c*n*‖x‖^2 →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k
        (smoothFiniteWave (realPolyEval (S p)) (fun j x => ζ x * realPolyEval (V p j) x) J n) x‖ ≤
        C*n^k*Real.exp (n*φ) := by
  dsimp only
  let K := 2*D+3*m+6
  let J := D+m+1
  let S := fun p => smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1)
  let V := fun p => uniformSmoothWaveAmplitudes (g p) (b p) (S p) (z p) K J
  have hu := generated_wave_uniform_jets g b hg hb hg0 hdg0 hgc hbc s hs z hz hz₀ Q hQ
    hsym hnull hQz K J (by dsimp [K]; omega) hP (isCompact_closedBall (0 : σ → ℝ) r)
  have hζB := uniformJetBounds_of_continuous_jets (fun _ : X => ζ)
    (fun k => (hζ.continuous_iteratedFDeriv (le_of_lt (WithTop.coe_lt_coe.mpr
      (ENat.natCast_lt_top k)))).comp continuous_snd) hP (isCompact_closedBall (0 : σ → ℝ) r)
  exact smooth_finite_wave_uniform_derivatives (fun p => realPolyEval (S p))
    (fun p j x => ζ x*realPolyEval (V p j) x)
    (fun p => contDiff_realPolyEval _) (fun p j => hζ.mul (contDiff_realPolyEval _)) m J
    (hu.1.mono subset_rfl Metric.ball_subset_closedBall)
    (fun j => (hζB.mul (fun _ => hζ) (fun _ => contDiff_realPolyEval _) (hu.2.2.2.2 j)).mono
      subset_rfl Metric.ball_subset_closedBall) c hc
end

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
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma contDiff_normalWaveProfile (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun w : NormalWaveParameter × PhaseSpace => normalWaveProfile g φ w.1 w.2) :=
  normal_profile_family_smooth g φ hφ

lemma continuous_normalWaveProfile_iteratedFDeriv
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : Set NormalWaveSpace) (k : ℕ) :
    Continuous (fun w : (metricFrameSet g K) × PhaseSpace =>
      iteratedFDeriv ℝ k (normalWaveProfile g φ w.1.val) w.2) := by
  have h : Continuous (fun w : NormalWaveParameter × PhaseSpace =>
      iteratedFDeriv ℝ k (normalWaveProfile g φ w.1) w.2) :=
    continuous_parameter_iteratedFDeriv
      (fun w : NormalWaveParameter × PhaseSpace => normalWaveProfile g φ w.1 w.2)
      (contDiff_normalWaveProfile g hφ) k
  exact h.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

end

open Set Filter Matrix
open scoped Topology ContDiff
theorem admissible_cutoff_wave_localized_derivatives {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (b : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
    (φ : X → PhaseSpace → ℝ) (hφ : ∀ p, ContDiff ℝ ∞ (φ p))
    (hφ0 : Continuous (fun p => φ p 0))
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (B C : ℝ) {κ : ℝ} (hκ : 0 < κ) (m D : ℕ) :
    ∃ r > 0, ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
      ∃ A > 0, ∀ p z Q, ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
        PhaseMatrixValid (actualHessianForm (φ p)) z κ C Q →
        ∀ n : ℝ, 1 ≤ n → ‖phaseRealVector z-gradient (φ p) 0‖ ≤ (Real.sqrt n)⁻¹ →
        ∀ x ∈ Metric.ball (0 : Fin 3 → ℝ) r, ∀ k ≤ m,
          ‖iteratedFDeriv ℝ k
            (canonicalCutoffWave (g p) (b p) (φ p 0 : ℂ) z Q ζ m D n) x‖ ≤
            A*n^k*Real.exp (n*φ p (WithLp.toLp 2 x))*Real.exp (-(κ/2)*n*‖x‖^2) := by
  let K := 2*D+3*m+6
  let J := D+m+1
  have hgj : ∀ i j k, k < K+J+1 → Continuous (fun p => iteratedFDeriv ℝ k (g p i j) 0) := by
    intro i j k _
    exact (hgc i j k).comp (continuous_id.prodMk continuous_const)
  obtain ⟨R,hR,hga⟩ := all_admissible_generated_gaussian g hg hg0 hdg0 φ hφ hφ0 hφ2
    (K+J+1) (by dsimp [K,J]; omega) hgj B C hκ
  let T := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  let a : ℝ := max ‖T‖ 1
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let r := min 1 (R/a)
  have hr : 0 < r := lt_min zero_lt_one (div_pos hR ha)
  refine ⟨r,hr,?_⟩
  intro ζ hζ hζ0
  let H := fun p => actualHessianForm (φ p)
  let W := boundedPhaseSet H B κ C
  have hW : IsCompact W := boundedPhaseSet_isCompact H (continuous_actualHessianForm φ hφ2) B κ C
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW
  let phaseProj : W → X := fun p => p.val.1.1
  let z : W → Fin 3 → ℂ := fun p => p.val.1.2
  let Q : W → ComplexPhaseMatrix := fun p => p.val.2
  have hphaseProj : Continuous phaseProj := (continuous_fst.comp continuous_fst).comp continuous_subtype_val
  have hz : Continuous z := (continuous_snd.comp continuous_fst).comp continuous_subtype_val
  have hQ : Continuous Q := continuous_snd.comp continuous_subtype_val
  have hn (p : W) : ∑ i, z p i*z p i = -1 := p.property.2.1
  have hv (p : W) : PhaseMatrixValid (H (phaseProj p)) (z p) κ C (Q p) := p.property.2.2
  have hgc' : ∀ i j k, Continuous (fun q : W × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (g (phaseProj q.1) i j) q.2) := by
    intro i j k
    exact (hgc i j k).comp ((hphaseProj.comp continuous_fst).prodMk continuous_snd)
  have hbc' : ∀ i k, Continuous (fun q : W × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (b (phaseProj q.1) i) q.2) := by
    intro i k
    exact (hbc i k).comp ((hphaseProj.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨A,hA,hres⟩ := generated_cutoff_wave_derivative_estimate
    (fun p : W => g (phaseProj p)) (fun p => b (phaseProj p)) (fun p => hg (phaseProj p)) (fun p => hb (phaseProj p))
    (fun p => hg0 (phaseProj p)) (fun p => hdg0 (phaseProj p)) hgc' hbc'
    (fun p => (φ (phaseProj p) 0 : ℂ)) (Complex.continuous_ofReal.comp (hφ0.comp hphaseProj))
    z (fun i => (continuous_apply i).comp hz) (fun p => phase_vector_ne_zero _ (hn p))
    Q (fun i j => (continuous_apply j).comp ((continuous_apply i).comp hQ))
    (fun p i j => congrFun (congrFun (hv p).1 j) i) hn
    (fun p k => phase_matrix_annihilation _ _ (hv p).2.1 k)
    ζ hζ hζ0 m D r (κ/2/2) (min_le_left _ _) (half_pos (half_pos hκ)) isCompact_univ
  refine ⟨A*Real.exp ((a-1)^2/(2*(κ/2))),mul_pos hA (Real.exp_pos _),?_⟩
  intro p z0 Q0 hz0 hn0 hQ0 n hn1 hlin x hx k hk
  let w : W := ⟨((p,z0),Q0),hz0,hn0,hQ0⟩
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn1
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hxnorm : ‖x‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hx
  have hTx : ‖T x‖ ≤ a*‖x‖ := (T.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x))
  have hxR : (WithLp.toLp 2 x : PhaseSpace) ∈ Metric.ball 0 R := by
    change ‖T x-0‖ < R
    rw [sub_zero]
    apply lt_of_le_of_lt hTx
    apply (mul_lt_mul_of_pos_left (hxnorm.trans_le (min_le_right _ _)) ha).trans_le
    exact le_of_eq (mul_div_cancel₀ R ha.ne')
  have hp := hga p z0 Q0 hz0 hn0 hQ0 (WithLp.toLp 2 x) hxR
  have hbound : n*((realPolyEval (smoothPhasePolynomial (g p) (φ p 0 : ℂ) z0 Q0 (K+J+1)) x).re-
      φ p (WithLp.toLp 2 x)) ≤ a*Real.sqrt n*‖x‖-κ*n*‖x‖^2 := by
    have hsq := Real.sq_sqrt hnpos.le
    have hnl : n*‖phaseRealVector z0-gradient (φ p) 0‖ ≤ Real.sqrt n := by
      calc
        _ ≤ n*(Real.sqrt n)⁻¹ := mul_le_mul_of_nonneg_left hlin hnpos.le
        _ = Real.sqrt n := by field_simp; nlinarith
    have hpl := mul_le_mul_of_nonneg_right hnl (norm_nonneg (T x))
    have hmax := mul_le_mul_of_nonneg_left hTx hspos.le
    have hnorm : ‖x‖ ≤ ‖T x‖ := norm_pi_le_euclidean x
    have hquad : ‖x‖^2 ≤ ‖T x‖^2 := by nlinarith [norm_nonneg x,norm_nonneg (T x)]
    have hm := mul_le_mul_of_nonneg_left hquad (mul_nonneg hκ.le hnpos.le)
    have hp' := mul_le_mul_of_nonneg_left hp hnpos.le
    change n*((realPolyEval _ x).re-φ p (WithLp.toLp 2 x)) ≤
      n*(‖phaseRealVector z0-gradient (φ p) 0‖*‖T x‖-κ*‖T x‖^2) at hp'
    nlinarith
  have hbound' : n*((realPolyEval (smoothPhasePolynomial (g p) (φ p 0 : ℂ) z0 Q0 (K+J+1)) x).re-
      (φ p (WithLp.toLp 2 x)-(κ/2)*‖x‖^2)) ≤ a*Real.sqrt n*‖x‖-(κ/2)*n*‖x‖^2 := by
    nlinarith
  have hbnd := gaussian_phase_coordinate_shift hnpos (half_pos hκ) hbound'
  have hh := hres w (mem_univ w) n hn1 x hx
    (φ p (WithLp.toLp 2 x)-(κ/2)*‖x‖^2+(a-1)^2/(2*(κ/2))/n) hbnd k hk
  change ‖iteratedFDeriv ℝ k
    (canonicalCutoffWave (g p) (b p) (φ p 0 : ℂ) z0 Q0 ζ m D n) x‖ ≤ _ at hh
  rw [gaussian_phase_shift_exp hnpos.ne'] at hh
  rw [show n*(φ p (WithLp.toLp 2 x)-(κ/2)*‖x‖^2) =
    n*φ p (WithLp.toLp 2 x)+(-(κ/2)*n*‖x‖^2) by ring,Real.exp_add] at hh
  convert hh using 1 <;> first | rfl | ring


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_NormalFamilyWaveLocalizedEstimates
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.coordinateRegionMeasure_finite _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples
theorem normal_family_wave_localized_estimates_oai (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
    (b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ)
    (hA : ContDiff ℝ ∞ A) (hb : ContDiff ℝ ∞ b)
    (hA0 : ∀ q ∈ metricFrameSet g K, ∀ i j, A (q,0) i j = if i = j then 1 else 0)
    (hAd : ∀ q ∈ metricFrameSet g K, ∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0)
    (B C : ℝ) {κ : ℝ} (hκ : 0 < κ) (m D : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
      ∃ T : ℝ, 0 < T ∧ ∀ q ∈ metricFrameSet g K, ∀ (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix), ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
        PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) z κ C Q →
        ∀ n : ℝ, 1 ≤ n →
        ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹ →
        ∀ x ∈ Metric.ball (0 : Fin 3 → ℝ) r, ∀ k ≤ m,
          ‖iteratedFDeriv ℝ k (normalFamilyWave g φ A b q z Q ζ m D n) x‖ ≤
              T*n^k*Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x))*
                Real.exp (-(κ/2)*n*‖x‖^2) ∧
          ‖iteratedFDeriv ℝ k (fun y =>
            waveCoordinateOperator (fun i => Pi.single i 1)
              (fun i j y => A (q,y) i j) (fun j y => b (q,y) j)
              (normalFamilyWave g φ A b q z Q ζ m D n) y +
            (n : ℂ)*((n : ℂ)+2)*normalFamilyWave g φ A b q z Q ζ m D n y) x‖ ≤
              T*(n^(D+1))⁻¹*Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x)) := by
  let X := metricFrameSet g K
  let : CompactSpace X := isCompact_iff_compactSpace.mp (metricFrameSet_isCompact g hK)
  let G : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ := fun q i j x => A (q.val,x) i j
  let β : X → Fin 3 → (Fin 3 → ℝ) → ℂ := fun q j x => b (q.val,x) j
  let Φ : X → PhaseSpace → ℝ := fun q => normalWaveProfile g φ q.val
  have hG (q : X) (i j : Fin 3) : ContDiff ℝ ∞ (G q i j) :=
    (contDiff_pi.mp (contDiff_pi.mp hA i) j).comp (contDiff_const.prodMk contDiff_id)
  have hβ (q : X) (j : Fin 3) : ContDiff ℝ ∞ (β q j) :=
    (contDiff_pi.mp hb j).comp (contDiff_const.prodMk contDiff_id)
  have hG0 (q : X) (i j : Fin 3) : G q i j 0 = if i = j then 1 else 0 := hA0 q.val q.property i j
  have hGd (q : X) (i j : Fin 3) : fderiv ℝ (G q i j) 0 = 0 := hAd q.val q.property i j
  have hGc (i j : Fin 3) (k : ℕ) : Continuous (fun w : X × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (G w.1 i j) w.2) := by
    exact (continuous_parameter_iteratedFDeriv (fun w => A w i j)
      (contDiff_pi.mp (contDiff_pi.mp hA i) j) k).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hβc (j : Fin 3) (k : ℕ) : Continuous (fun w : X × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (β w.1 j) w.2) := by
    exact (continuous_parameter_iteratedFDeriv (fun w => b w j)
      (contDiff_pi.mp hb j) k).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hΦ (q : X) : ContDiff ℝ ∞ (Φ q) :=
    (contDiff_normalWaveProfile g hφ).comp (contDiff_const.prodMk contDiff_id)
  have hΦ0 : Continuous (fun q : X => Φ q 0) :=
    (contDiff_normalWaveProfile g hφ).continuous.comp
      (continuous_subtype_val.prodMk continuous_const)
  have hΦ2 : Continuous (fun w : X × PhaseSpace => iteratedFDeriv ℝ 2 (Φ w.1) w.2) :=
    continuous_normalWaveProfile_iteratedFDeriv g hφ K 2
  obtain ⟨r1,hr1,he1⟩ := admissible_cutoff_wave_localized_derivatives G β hG hβ hG0 hGd hGc hβc
    Φ hΦ hΦ0 hΦ2 B C hκ m D
  obtain ⟨r2,hr2,he2⟩ := admissible_cutoff_wave_residual G β hG hβ hG0 hGd hGc hβc
    Φ hΦ hΦ0 hΦ2 B C hκ m D
  refine ⟨min r1 r2,lt_min hr1 hr2,?_⟩
  intro ζ hζ hζ0
  obtain ⟨T1,hT1,hb1⟩ := he1 ζ hζ hζ0
  obtain ⟨T2,hT2,hb2⟩ := he2 ζ hζ hζ0
  refine ⟨max T1 T2,lt_of_lt_of_le hT1 (le_max_left _ _),?_⟩
  intro q hq z Q hz hn hQ n hn1 hlin x hx k hk
  have hx1 := Metric.ball_subset_ball (min_le_left r1 r2) hx
  have hx2 := Metric.ball_subset_ball (min_le_right r1 r2) hx
  refine ⟨(hb1 ⟨q,hq⟩ z Q hz hn hQ n hn1 hlin x hx1 k hk).trans ?_,
    (hb2 ⟨q,hq⟩ z Q hz hn hQ n hn1 hlin x hx2 k hk).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left T1 T2) (pow_nonneg (le_trans zero_le_one hn1) _))
        (Real.exp_pos _).le) (Real.exp_pos _).le
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right T1 T2)
        (inv_nonneg.mpr (pow_nonneg (le_trans zero_le_one hn1) _))) (Real.exp_pos _).le
end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.normal_family_wave_localized_estimates_oai := @OAI.YauCounterexamples.normal_family_wave_localized_estimates_oai
