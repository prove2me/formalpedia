-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_center_polynomial_fourier_formula
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T09:39:58.898501+00:00
-- url     : https://prove2.me/submissions/1e4c5cc6-0aa2-4167-a5ca-2dcaab0e79ba

import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier
import Theorems.Thm_TaoFivePrimes_rh_fast_gaussian_polynomial_fourier
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic.ComputeDegree
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Finset Polynomial MeasureTheory
open scoped FourierTransform
namespace RHFastFormulaPolynomialAlgebra
open RHFastGaussianWindow
lemma delta_eval (T:Nat) (t:ℝ) :
 (deltaPolynomial T).eval ((t:ℂ)/256)=delta T t := by
 have hu:128*I*((t:ℂ)/256)=((t/2:ℝ):ℂ)*I := by push_cast;ring
 have hlog (v u:ℂ):
  (∑j∈Finset.range 7,((-1:ℂ)^(j+1)/(j:ℂ))*(u*v⁻¹)^j)=Complex.logTaylor 7 (u/v) := by
  unfold Complex.logTaylor
  apply Finset.sum_congr rfl
  intro j hj
  simp only [div_eq_mul_inv]
  ring
 unfold deltaPolynomial
 simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_sub,
  Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_finsetSum,
  Polynomial.eval_pow,Polynomial.eval_one,Polynomial.eval_neg]
 rw [hu,hlog]
 unfold delta
 simp only [div_eq_mul_inv,neg_mul]
 push_cast
 ring
lemma delta_degree (T:Nat) : (deltaPolynomial T).natDegree≤7 := by
 unfold deltaPolynomial
 simp only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty]
 compute_degree
lemma proxy_degree (T:Nat) : (proxyPolynomial T).natDegree≤28 := by
 unfold proxyPolynomial
 apply Polynomial.natDegree_sum_le_of_forall_le
 intro r hr
 have hr4:r≤4:=by have :=Finset.mem_range.mp hr;omega
 apply Polynomial.natDegree_mul_le.trans
 simp only [Polynomial.natDegree_C,add_zero]
 exact (Polynomial.natDegree_pow_le_of_le r (delta_degree T)).trans (by omega)
lemma proxy_eval (T:Nat) (t:ℝ) :
 (proxyPolynomial T).eval ((t:ℂ)/256)=exponentialPolynomial (delta T t) := by
 simp only [proxyPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_mul,
  Polynomial.eval_pow,Polynomial.eval_C,delta_eval]
 simp only [exponentialPolynomial,div_eq_mul_inv]
end RHFastFormulaPolynomialAlgebra


namespace RHFastWindowFourierFormula
open RHFastGaussianWindow
noncomputable def mono (T n:Nat) (t:ℝ) : ℂ := (t:ℂ)^n*carrier T t
noncomputable def coefficient (T k d:Nat) : ℂ :=
 anchor T*(proxyPolynomial T).coeff d*
  ((-2*(Real.pi:ℂ)*I)^k/((k.factorial:ℂ)*(512:ℂ)^k*(256:ℂ)^d))
lemma mono_integrable (T n:Nat) : Integrable (mono T n) := by
 have hr:=integrable_rpow_mul_exp_neg_mul_sq
  (b:=(1/800:ℝ)) (s:=(n:ℝ)) (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) n])
 have hi:Integrable (fun t:ℝ=>|t|^n*Real.exp (-t^2/800)) := by
  convert hr.norm using 1
  ext t
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),Real.rpow_natCast,abs_pow]
  congr 2
  ring
 apply hi.mono'
 · exact (by unfold mono carrier;fun_prop : Continuous (mono T n)).aestronglyMeasurable
 · filter_upwards [] with t
   simp only [mono,carrier,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp]
   have he:((( -t^2/800:ℝ):ℂ)+I*(omega T:ℂ)*t).re= -t^2/800 := by
    simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im]
    ring
   rw [he]
lemma expansion (T k:Nat) (t:ℝ) : momentProxy T k t=
 ∑d∈Finset.range 29,coefficient T k d*mono T (d+k) t := by
 have hq:exponentialPolynomial (delta T t)=
   ∑d∈Finset.range 29,(proxyPolynomial T).coeff d*((t:ℂ)/256)^d := by
  rw [←RHFastFormulaPolynomialAlgebra.proxy_eval]
  exact Polynomial.eval_eq_sum_range' (by have h:=RHFastFormulaPolynomialAlgebra.proxy_degree T;omega) _
 unfold momentProxy proxy
 rw [hq,Finset.mul_sum,Finset.sum_mul]
 apply Finset.sum_congr rfl
 intro d hd
 simp only [coefficient,mono,momentFactor,pow_add,mul_pow,div_pow]
 have hk:(k.factorial:ℂ)≠0:=by exact_mod_cast Nat.factorial_ne_zero k
 field_simp [hk] <;> ring
lemma proxy_integrable (T k:Nat) : Integrable (momentProxy T k) := by
 have he:momentProxy T k=(fun t:ℝ=>∑d∈Finset.range 29,coefficient T k d*mono T (d+k) t):=
  funext (expansion T k)
 rw [he]
 exact integrable_finsetSum _ (fun d hd=>(mono_integrable T (d+k)).const_mul _)
lemma twist_integrable {g:ℝ→ℂ} (hg:Integrable g) (x:ℝ) :
 Integrable (fun t:ℝ=>Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)*g t) := by
 apply hg.norm.mono'
 · exact (by fun_prop : Continuous (fun t:ℝ=>Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I))).aestronglyMeasurable.mul hg.aestronglyMeasurable
 · filter_upwards [] with t
   simp [Complex.norm_exp]
lemma fourier_expansion (T k:Nat) (x:ℝ) :
 𝓕 (momentProxy T k) x=∑d∈Finset.range 29,coefficient T k d*𝓕 (mono T (d+k)) x := by
 rw [Real.fourier_real_eq_integral_exp_smul]
 simp only [smul_eq_mul]
 simp_rw [expansion,Finset.mul_sum]
 rw [integral_finsetSum _ (fun d hd=>twist_integrable ((mono_integrable T (d+k)).const_mul _) x)]
 apply Finset.sum_congr rfl
 intro d hd
 rw [Real.fourier_real_eq_integral_exp_smul]
 simp only [smul_eq_mul]
 simp_rw [mul_left_comm _ (coefficient T k d)]
 exact integral_const_mul _ _
lemma real_eval (n:Nat) (x:ℝ) :
 Polynomial.aeval (x:ℂ) (Polynomial.hermite n)=
   (((Polynomial.hermite n).eval₂ (Int.castRingHom ℝ) x:ℝ):ℂ) := by
 rw [Polynomial.aeval_def]
 have h:=Polynomial.hom_eval₂ (p:=Polynomial.hermite n) (f:=Int.castRingHom ℝ)
   (g:=Complex.ofRealHom) x
 convert! h.symm using 1
lemma mono_fourier (T n:Nat) (x:ℝ) :
 𝓕 (mono T n) x=(Real.sqrt (2*Real.pi):ℂ)*(20:ℂ)*(-I*(20:ℂ))^n*
  (((Polynomial.hermite n).eval₂ (Int.castRingHom ℝ) (frequency T x):ℝ):ℂ)*
  (Real.exp (-(frequency T x)^2/2):ℂ) := by
 have h:=TaoFivePrimes.rh_fast_gaussian_polynomial_fourier 20 (omega T) x (by norm_num) n
 have hf:(fun t:ℝ=>(t:ℂ)^n*Complex.exp (-(t:ℂ)^2/(2*(20:ℂ)^2)+I*(omega T:ℂ)*t))=mono T n := by
  funext t
  unfold mono carrier
  congr 2
  push_cast
  norm_num
 norm_num only [Complex.ofReal_ofNat] at hf h
 rw [hf] at h
 have he:Complex.exp (-((frequency T x:ℝ):ℂ)^2/2)=
   (Real.exp (-(frequency T x)^2/2):ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring
 change 𝓕 (mono T n) x=(Real.sqrt (2*Real.pi):ℂ)*20*(-I*(20:ℂ))^n*
  Polynomial.aeval ((frequency T x:ℝ):ℂ) (Polynomial.hermite n)*
  Complex.exp (-((frequency T x:ℝ):ℂ)^2/2) at h
 rw [real_eval,he] at h
 exact h
lemma constants (k d:Nat) :
 ((-2*(Real.pi:ℂ)*I)^k/((k.factorial:ℂ)*(512:ℂ)^k*(256:ℂ)^d))*(-I*(20:ℂ))^(d+k)=
 (((-Real.pi:ℝ):ℂ)^k/(k.factorial:ℂ))*(-I)^d*(5/64:ℂ)^(d+k) := by
 have h1:(-2*(Real.pi:ℂ)*I)*(-I*(20:ℂ))/512=((-Real.pi:ℝ):ℂ)*(5/64:ℂ) := by
  push_cast
  ring_nf
  simp only [I_sq]
  ring
 have h2:(-I*(20:ℂ))/256=(-I)*(5/64:ℂ):=by ring
 calc
  _ = ((((-2*(Real.pi:ℂ)*I)*(-I*(20:ℂ)))/512)^k/(k.factorial:ℂ))*
    ((-I*(20:ℂ))/256)^d := by
   simp only [pow_add,mul_pow,div_pow]
   have hk:(k.factorial:ℂ)≠0:=by exact_mod_cast Nat.factorial_ne_zero k
   field_simp [hk] <;> ring
  _ = _ := by
   rw [h1,h2]
   simp only [mul_pow,pow_add,div_eq_mul_inv]
   ring
lemma formula (T k:Nat) (x:ℝ) :
 𝓕 (momentProxy T k) x=fourierFormula T k x := by
 rw [fourier_expansion]
 simp_rw [mono_fourier]
 unfold fourierFormula
 simp only [Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro d hd
 unfold coefficient scaledHermite
 simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_ofNat]
 calc
  _ = anchor T*(proxyPolynomial T).coeff d*
    (((-2*(Real.pi:ℂ)*I)^k/((k.factorial:ℂ)*(512:ℂ)^k*(256:ℂ)^d))*(-I*(20:ℂ))^(d+k))*
    (Real.sqrt (2*Real.pi):ℂ)*20*
    (((Polynomial.hermite (d+k)).eval₂ (Int.castRingHom ℝ) (frequency T x):ℝ):ℂ)*
    (Real.exp (-(frequency T x)^2/2):ℂ) := by ring
  _ = _ := by rw [constants];ring
end RHFastWindowFourierFormula

theorem solution (T k:Nat) : MeasureTheory.Integrable (RHFastGaussianWindow.momentProxy T k) ∧
 ∀x:ℝ,𝓕 (RHFastGaussianWindow.momentProxy T k) x=RHFastGaussianWindow.fourierFormula T k x :=
 ⟨RHFastWindowFourierFormula.proxy_integrable T k,RHFastWindowFourierFormula.formula T k⟩
#print axioms solution
