-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P56.hybrid_entropy_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:38:39.718949+00:00
-- url     : https://prove2.me/submissions/a425c438-7374-42ad-a81d-f9985f19f045

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

open scoped Matrix in
lemma g53_cfc_trace {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

open Polynomial in
lemma g53h_trace_cfc_two {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (a b : ℝ)
    (hc : A.charpoly = (X - C (a : ℂ)) * (X - C (b : ℂ))) (f : ℝ → ℝ) :
    (cfc f A).trace = ((f a + f b : ℝ) : ℂ) := by
  have hr : A.charpoly.roots = (a : ℂ) ::ₘ {(b : ℂ)} := by
    rw [hc, Polynomial.roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
      roots_X_sub_C, roots_X_sub_C]; rfl
  rw [g53_cfc_trace hA]
  have h := hA.roots_charpoly_eq_eigenvalues
  rw [hr] at h
  have h2 := congrArg (fun m : Multiset ℂ => (m.map (fun z => ((f z.re : ℝ) : ℂ))).sum) h
  simp only [Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons, Multiset.sum_singleton,
    Multiset.map_map] at h2
  rw [Finset.sum_eq_multiset_sum]
  simp only [Complex.ofReal_re] at h2
  push_cast
  rw [h2]; rfl

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Section VI C, pp.14–15, Eqs.(51)–(52): exact hybrid average and entropy formula,
symmetric in x and 1-x. Parameters at zero and one are included. -/
theorem solution (q qprime x : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hqp : qprime ∈ Set.Icc (0 : ℝ) 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    average (hybridBob q) (bernoulli x) =
      Matrix.diagonal (fun b => (bernoulli (binaryConvolution x q) b : ℂ)) ∧
    average (hybridEve qprime) (bernoulli x) =
      (fun j k : Bool => if j = k then (if j then (1 - qprime : ℂ) else (qprime : ℂ))
        else (((1 - 2 * x) * Real.sqrt (qprime * (1 - qprime)) : ℝ) : ℂ)) ∧
    (∀ y : ℂ,
      let s := Real.sqrt (1 - 16 * qprime * (1 - qprime) * x * (1 - x))
      Matrix.det (y • (1 : Matrix Bool Bool ℂ) - average (hybridEve qprime) (bernoulli x)) =
        (y - (((1 - s) / 2 : ℝ) : ℂ)) * (y - (((1 + s) / 2 : ℝ) : ℂ))) ∧
    binaryDelta (hybridBob q) (hybridEve qprime) x = hybridFormula q qprime x ∧
    hybridFormula q qprime (1 - x) = hybridFormula q qprime x := by
  obtain ⟨hq0, hq1⟩ := hq; obtain ⟨hp0, hp1⟩ := hqp; obtain ⟨hx0, hx1⟩ := hx
  have hsq : Real.sqrt qprime * Real.sqrt (1 - qprime) = Real.sqrt (qprime * (1 - qprime)) :=
    (Real.sqrt_mul hp0 _).symm
  have hB : average (hybridBob q) (bernoulli x) =
      Matrix.diagonal (fun b => (bernoulli (binaryConvolution x q) b : ℂ)) := by
    ext i j
    cases i <;> cases j <;> simp [average, hybridBob, P56.bernoulli, binaryConvolution, Fintype.sum_bool, Matrix.add_apply,
      Matrix.diagonal] <;> ring
  have hE : average (hybridEve qprime) (bernoulli x) =
      (fun j k : Bool => if j = k then (if j then (1 - qprime : ℂ) else (qprime : ℂ))
        else (((1 - 2 * x) * Real.sqrt (qprime * (1 - qprime)) : ℝ) : ℂ)) := by
    have e1 : (Real.sqrt qprime : ℂ) * (Real.sqrt qprime : ℂ) = qprime := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp0]
    have e2 : (Real.sqrt (1 - qprime) : ℂ) * (Real.sqrt (1 - qprime) : ℂ) = 1 - qprime := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]; push_cast; ring
    have e3 : (Real.sqrt qprime : ℂ) * (Real.sqrt (1 - qprime) : ℂ) = Real.sqrt (qprime * (1 - qprime)) := by
      rw [← hsq]; push_cast; ring
    ext i j
    simp only [average, Fintype.sum_bool, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    unfold hybridEve P56.bernoulli
    cases i <;> cases j <;> simp [Complex.conj_ofReal]
    · linear_combination (1 - (x:ℂ) + x) * e1 - e1 + e1
    · linear_combination (1 - 2 * (x:ℂ)) * e3
    · linear_combination (1 - 2 * (x:ℂ)) * e3
    · linear_combination e2
  have hs2 : Real.sqrt (1 - 16 * qprime * (1 - qprime) * x * (1 - x)) ^ 2
      = 1 - 16 * qprime * (1 - qprime) * x * (1 - x) := by
    apply Real.sq_sqrt
    nlinarith [mul_nonneg hp0 (sub_nonneg.2 hp1), mul_nonneg hx0 (sub_nonneg.2 hx1),
      sq_nonneg (2 * qprime - 1), sq_nonneg (2 * x - 1),
      mul_nonneg (mul_nonneg hp0 (sub_nonneg.2 hp1)) (mul_nonneg hx0 (sub_nonneg.2 hx1))]
  have hsq2 : Real.sqrt (qprime * (1 - qprime)) ^ 2 = qprime * (1 - qprime) :=
    Real.sq_sqrt (mul_nonneg hp0 (by linarith))
  have hdet : ∀ y : ℂ,
      let s := Real.sqrt (1 - 16 * qprime * (1 - qprime) * x * (1 - x))
      Matrix.det (y • (1 : Matrix Bool Bool ℂ) - average (hybridEve qprime) (bernoulli x)) =
        (y - (((1 - s) / 2 : ℝ) : ℂ)) * (y - (((1 + s) / 2 : ℝ) : ℂ)) := by
    intro y s
    have entry : ∀ i j, (y • (1 : Matrix Bool Bool ℂ) - average (hybridEve qprime) (P56.bernoulli x)) i j
        = (if i = j then y else 0) - average (hybridEve qprime) (P56.bernoulli x) i j := by
      intro i j; rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [← Matrix.det_submatrix_equiv_self finTwoEquiv, Matrix.det_fin_two]
    simp only [Matrix.submatrix_apply]
    rw [entry, entry, entry, entry, hE]
    simp [finTwoEquiv]
    have hs2' : ((s : ℂ)) ^ 2 = 1 - 16 * qprime * (1 - qprime) * x * (1 - x) := by
      exact_mod_cast hs2
    have hsq2' : ((Real.sqrt (qprime * (1 - qprime)) : ℂ)) ^ 2 = qprime * (1 - qprime) := by
      exact_mod_cast hsq2
    linear_combination (1/4 : ℂ) * hs2' - (1 - 2 * (x:ℂ))^2 * hsq2'
  refine ⟨hB, hE, hdet, ?_, ?_⟩
  · set c := binaryConvolution x q with hc
    set s := Real.sqrt (1 - 16 * qprime * (1 - qprime) * x * (1 - x)) with hs
    have hBh : (average (hybridBob q) (P56.bernoulli x)).IsHermitian := by
      rw [hB]; exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)
    have hEh : (average (hybridEve qprime) (P56.bernoulli x)).IsHermitian := by
      ext i j; rw [Matrix.conjTranspose_apply, hE]
      cases i <;> cases j <;> simp [Complex.conj_ofReal]
    have hcB : (average (hybridBob q) (P56.bernoulli x)).charpoly =
        (Polynomial.X - Polynomial.C ((c : ℝ) : ℂ)) * (Polynomial.X - Polynomial.C (((1 - c : ℝ)) : ℂ)) := by
      rw [hB, Matrix.charpoly_diagonal, Fintype.prod_bool]
      simp [P56.bernoulli]
    have hcE : (average (hybridEve qprime) (P56.bernoulli x)).charpoly =
        (Polynomial.X - Polynomial.C ((((1 - s) / 2 : ℝ)) : ℂ)) *
          (Polynomial.X - Polynomial.C ((((1 + s) / 2 : ℝ)) : ℂ)) := by
      apply Polynomial.funext; intro y
      rw [Matrix.eval_charpoly, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, hdet y]
      simp
    unfold binaryDelta delta entropy
    rw [g53h_trace_cfc_two hBh _ _ hcB, g53h_trace_cfc_two hEh _ _ hcE]
    simp only [Complex.ofReal_re]
    unfold hybridFormula
    rw [← hc, ← hs]
    have h1 : 1 - (1 - s) / 2 = (1 + s) / 2 := by ring
    simp only [Real.binEntropy, Real.log_inv, h1]
    ring
  · unfold hybridFormula
    rw [show binaryConvolution (1 - x) q = 1 - binaryConvolution x q by unfold binaryConvolution; ring,
      Real.binEntropy_one_sub,
      show (1 - 16 * qprime * (1 - qprime) * (1 - x) * (1 - (1 - x))) =
        (1 - 16 * qprime * (1 - qprime) * x * (1 - x)) by ring]



end

