-- Prove2me | solution 1 for WeierstrassEllipticZeta.triangular_multiplication_determinant
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T23:33:10.154902+00:00
-- url     : https://prove2.me/submissions/2be2c816-9b70-44e3-b403-0757a9b58407

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Tactic.Ring

noncomputable section


theorem solution
    (V : Finset (Fin 4 → ℂ)) (e : V → ℕ)
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (hvanish : ∀ p ∈ I, ∀ v : V, 0 < e v → MvPolynomial.eval v.val p = 0)
    (M : Polynomial ℂ)
    (hM : M = ∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ e v)
    (r : Fin 3 → Polynomial ℂ)
    (hmem : ∀ p : MvPolynomial (Fin 4) ℂ,
      p ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) p)
    (ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ]
      Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ)
    (hρ : ∀ p : MvPolynomial (Fin 4) ℂ,
      ρ p = Polynomial.aeval (ρ (MvPolynomial.X (0 : Fin 4)))
        (MvPolynomial.aeval (Fin.cons Polynomial.X r) p))
    (hchar : (ρ (MvPolynomial.X (0 : Fin 4))).charpoly = M) :
    (∀ p : MvPolynomial (Fin 4) ℂ,
      (ρ p).det = ∏ v : V, (MvPolynomial.eval v.val p) ^ e v) ∧
    (∀ p : MvPolynomial (Fin 4) ℂ,
      IsUnit (ρ p) ↔ ∀ v : V, 0 < e v → MvPolynomial.eval v.val p ≠ 0) := by
  classical
  let A := ρ (MvPolynomial.X (0 : Fin 4))
  let φ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Polynomial ℂ :=
    MvPolynomial.aeval (Fin.cons Polynomial.X r)
  let E : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
    Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
  have hE : φ.comp E = AlgHom.id ℂ (Polynomial ℂ) := by
    ext
    simp [φ, E]
  have hEapp (f : Polynomial ℂ) : φ (E f) = f := AlgHom.congr_fun hE f
  have heval (p : MvPolynomial (Fin 4) ℂ) (v : V) (hv : 0 < e v) :
      (φ p).eval (v.val 0) = MvPolynomial.eval v.val p := by
    have hp : p - E (φ p) ∈ I := by
      apply (hmem _).mpr
      change M ∣ φ (p - E (φ p))
      simp only [map_sub, hEapp, sub_self, dvd_zero]
    have hEv : (MvPolynomial.eval v.val).comp E.toRingHom =
        Polynomial.evalRingHom (v.val 0) := by
      ext <;> simp [E]
    have hEvapp : MvPolynomial.eval v.val (E (φ p)) = (φ p).eval (v.val 0) :=
      RingHom.congr_fun hEv (φ p)
    have h := hvanish _ hp v hv
    rw [map_sub, hEvapp] at h
    exact (sub_eq_zero.mp h).symm
  have hdim : M.natDegree = ∑ v : V, e v := by
    rw [hM, Polynomial.natDegree_prod_of_monic]
    · simp
    · intro v _
      exact (Polynomial.monic_X_sub_C _).pow _
  have hlinear (a : ℂ) :
      (Polynomial.aeval A (Polynomial.X + Polynomial.C a)).det =
        ∏ v : V, (v.val 0 + a) ^ e v := by
    have hA : A.charpoly = M := hchar
    have hmat : Polynomial.aeval A (Polynomial.X + Polynomial.C a) =
        -(Matrix.scalar _ (-a) - A) := by
      simp [sub_eq_add_neg, Matrix.algebraMap_eq_diagonal, Matrix.scalar]
    rw [hmat, Matrix.det_neg, ← Matrix.eval_charpoly, hA, Fintype.card_fin, hdim, hM]
    simp only [Polynomial.eval_prod, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v _
    rw [← mul_pow]
    congr 1
    ring
  have hdet (f : Polynomial ℂ) :
      (Polynomial.aeval A f).det = ∏ v : V, (f.eval (v.val 0)) ^ e v := by
    have hf := IsAlgClosed.splits f
    induction hf using Submonoid.closure_induction with
    | mem f hf =>
      obtain (⟨a, rfl⟩ | ⟨a, rfl⟩) := hf
      · simp [Matrix.algebraMap_eq_diagonal, hdim, Finset.prod_pow_eq_pow_sum]
      · simpa using hlinear a
    | one => simp
    | mul f g _ _ hf hg =>
      simp only [map_mul, Matrix.det_mul, hf, hg, Polynomial.eval_mul, mul_pow,
        Finset.prod_mul_distrib]
  have hresult (p : MvPolynomial (Fin 4) ℂ) :
      (ρ p).det = ∏ v : V, (MvPolynomial.eval v.val p) ^ e v := by
    rw [hρ p]
    change (Polynomial.aeval A (φ p)).det = _
    rw [hdet]
    apply Finset.prod_congr rfl
    intro v _
    by_cases hv : e v = 0
    · simp [hv]
    · rw [heval p v (Nat.pos_of_ne_zero hv)]
  refine ⟨hresult, fun p => ?_⟩
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, hresult]
  simp only [Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const]
  constructor
  · intro h v hv heq
    have := h v
    simp [heq, Nat.ne_of_gt hv] at this
  · intro h v
    by_cases hv : e v = 0
    · simp [hv]
    · exact pow_ne_zero _ (h v (Nat.pos_of_ne_zero hv))

