-- Prove2me | solution 1 for TranscendenceTheory.polynomial_ode_iterated_deriv
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T11:19:46.956381+00:00
-- url     : https://prove2.me/submissions/72c437d8-36b3-487e-bdec-29d9368da74a

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FinCases

noncomputable section

open MvPolynomial Filter
open scoped Topology

private lemma pderiv_degree {σ : Type} (p : MvPolynomial σ ℤ) (i : σ)
    (h : pderiv i p ≠ 0) : (pderiv i p).totalDegree + 1 ≤ p.totalDegree := by
  classical
  obtain ⟨m, hm, heq⟩ := (pderiv i p).support.exists_mem_eq_sup
    (by simpa using h) (fun m => m.sum fun _ e => e)
  have hcoeff : p.coeff (m + Finsupp.single i 1) ≠ 0 := by
    have := mem_support_iff.mp hm
    rw [coeff_pderiv] at this
    exact (mul_ne_zero_iff.mp this).1
  have hle := le_totalDegree (mem_support_iff.mpr hcoeff)
  simpa [totalDegree, heq, Finsupp.sum_add_index'] using hle

private lemma derivation_sum_apply {σ : Type} [Fintype σ]
    (F : σ → Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (p : MvPolynomial σ ℤ) : (∑ i, F i) p = ∑ i, F i p := by
  change (Derivation.coeFnAddMonoidHom (∑ i, F i)) p = _
  rw [map_sum, Finset.sum_apply]
  rfl

private lemma derivation_degree {σ : Type} [Fintype σ]
    (D : Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (hD : ∀ i, (D (X i)).totalDegree ≤ 2) (p : MvPolynomial σ ℤ) :
    (D p).totalDegree ≤ p.totalDegree + 1 := by
  classical
  have hrepr : D = ∑ i, D (X i) • pderiv i := by
    apply MvPolynomial.derivation_ext
    intro j
    simp [derivation_sum_apply, Derivation.smul_apply, Pi.single_apply]
  have hvalue : D p = ∑ i, D (X i) * pderiv i p := by
    conv_lhs => rw [hrepr]
    simp [derivation_sum_apply]
  rw [hvalue]
  apply totalDegree_finsetSum_le
  intro i _
  by_cases hi : pderiv i p = 0
  · simp [hi]
  have hp := pderiv_degree p i hi
  have hmul := totalDegree_mul (D (X i)) (pderiv i p)
  have := hD i
  omega

private lemma hasDerivAt_eval_ode {σ : Type}
    (D : Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (f : σ → ℂ → ℂ) (z : ℂ)
    (hf : ∀ i, HasDerivAt (f i)
      (eval₂ (Int.castRingHom ℂ) (fun i => f i z) (D (X i))) z)
    (p : MvPolynomial σ ℤ) :
    HasDerivAt (fun w => eval₂ (Int.castRingHom ℂ) (fun i => f i w) p)
      (eval₂ (Int.castRingHom ℂ) (fun i => f i z) (D p)) z := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [derivation_C, eval₂_C, eval₂_zero]
    exact hasDerivAt_const z (a : ℂ)
  | add p q hp hq => simpa [Pi.add_apply] using! hp.add hq
  | mul_X p i hp =>
    simpa [D.leibniz, smul_eq_mul, add_comm, mul_comm, Pi.mul_apply] using! hp.mul (hf i)

/-- Differentiation along a quadratic polynomial ODE preserves integer polynomial
presentations, increasing their total degree by at most one at each step. -/
theorem solution {σ : Type} [Fintype σ]
    (D : Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (hD : ∀ i, (D (X i)).totalDegree ≤ 2)
    (U : Set ℂ) (hU : IsOpen U) (f : σ → ℂ → ℂ)
    (hf : ∀ z ∈ U, ∀ i, HasDerivAt (f i)
      (eval₂ (Int.castRingHom ℂ) (fun i => f i z) (D (X i))) z)
    (p : MvPolynomial σ ℤ) (n : ℕ) :
    (D^[n] p).totalDegree ≤ p.totalDegree + n ∧
      ∀ z ∈ U, iteratedDeriv n
        (fun w => eval₂ (Int.castRingHom ℂ) (fun i => f i w) p) z =
          eval₂ (Int.castRingHom ℂ) (fun i => f i z) (D^[n] p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    constructor
    · rw [Function.iterate_succ_apply']
      exact (derivation_degree D hD _).trans (by omega)
    · intro z hz
      rw [iteratedDeriv_succ, Function.iterate_succ_apply']
      have heq : iteratedDeriv n
          (fun w => eval₂ (Int.castRingHom ℂ) (fun i => f i w) p) =ᶠ[𝓝 z]
          (fun w => eval₂ (Int.castRingHom ℂ) (fun i => f i w) (D^[n] p)) :=
        Filter.Eventually.mono (hU.mem_nhds hz) fun w hw => ih.2 w hw
      rw [heq.deriv_eq]
      exact (hasDerivAt_eval_ode D f z (hf z hz) _).deriv

