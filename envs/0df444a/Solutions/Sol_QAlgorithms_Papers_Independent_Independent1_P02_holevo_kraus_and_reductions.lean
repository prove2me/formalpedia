-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P02.holevo_kraus_and_reductions
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:05:50.239122+00:00
-- url     : https://prove2.me/submissions/42e607a2-c5ee-4458-9608-770a12a9fc5b

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
import Mathlib.Analysis.Matrix.Order

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder ComplexConjugate
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Independent1.P02

private lemma outer_star {d : ℕ} (v w : StateVector d) :
    (outerOperator v w)ᴴ = outerOperator w v := by
  ext i j
  simp [outerOperator, mul_comm]

private lemma outer_self {d : ℕ} (v : StateVector d) :
    outerOperator v v = pureDensity v := rfl

private lemma outer_sandwich {d : ℕ} (v w : StateVector d) (X : Algebra d) :
    outerOperator v w * X * (outerOperator v w)ᴴ =
      (pureDensity w * X).trace • pureDensity v := by
  ext i j
  simp only [outerOperator, pureDensity, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    starRingEnd_apply, star_mul, star_star, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

private lemma basis_pure_sum {d : ℕ}
    (e : OrthonormalBasis (Fin d) ℂ (StateVector d)) : ∑ i, pureDensity (e i) = 1 := by
  ext a b
  have h := congrArg (fun x : StateVector d => x a) (e.sum_repr' (ket b))
  simpa [pureDensity, PiLp.inner_apply, ket, Matrix.one_apply, mul_comm,
    eq_comm, WithLp.ofLp_sum, Matrix.sum_apply, Matrix.of_apply] using h

private lemma basis_state {d : ℕ}
    (e : OrthonormalBasis (Fin d) ℂ (StateVector d)) (i : Fin d) : IsState (e i) :=
  e.orthonormal.norm_eq_one i

private lemma basis_trace {d : ℕ}
    (e : OrthonormalBasis (Fin d) ℂ (StateVector d)) (X : Algebra d) :
    ∑ i, (pureDensity (e i) * X).trace = X.trace := by
  rw [← Matrix.trace_sum, ← Finset.sum_mul, basis_pure_sum, Matrix.one_mul]

private lemma outer_sum_left {d : ℕ}
    (e : OrthonormalBasis (Fin d) ℂ (StateVector d)) (w : StateVector d) (X : Algebra d) :
    ∑ i, outerOperator (e i) w * X * (outerOperator (e i) w)ᴴ =
      (pureDensity w * X).trace • (1 : Algebra d) := by
  simp_rw [outer_sandwich]
  rw [← Finset.smul_sum, basis_pure_sum]

private lemma outer_sum_right {d : ℕ}
    (f : OrthonormalBasis (Fin d) ℂ (StateVector d)) (v : StateVector d) (X : Algebra d) :
    ∑ j, outerOperator v (f j) * X * (outerOperator v (f j))ᴴ =
      X.trace • pureDensity v := by
  simp_rw [outer_sandwich]
  rw [← Finset.sum_smul, basis_trace]

private lemma sqrt_herm {d : ℕ} (A : Algebra d) :
    (cfc Real.sqrt A).IsHermitian :=
  (cfc_nonneg (a := A) (fun x _ => Real.sqrt_nonneg x)).posSemidef.isHermitian

private lemma sqrt_sq {d : ℕ} (A : Algebra d) (hA : A.PosSemidef) :
    cfc Real.sqrt A * cfc Real.sqrt A = A := by
  simpa only [CFC.sqrt_eq_real_sqrt A hA.nonneg, cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), pow_two] using CFC.sq_sqrt A hA.nonneg


private lemma sum_sandwich {d : ℕ} {K : Type*} [Fintype K]
    (S T X : Algebra d) (A : K → Algebra d) :
    ∑ i, (S * A i * T) * X * (S * A i * T)ᴴ =
      S * (∑ i, A i * (T * X * Tᴴ) * (A i)ᴴ) * Sᴴ := by
  simp [Matrix.conjTranspose_mul, Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]

private lemma two_basis_sandwich {d : ℕ}
    (e f : OrthonormalBasis (Fin d) ℂ (StateVector d)) (X : Algebra d) :
    ∑ i, ∑ j, outerOperator (e i) (f j) * X * (outerOperator (e i) (f j))ᴴ =
      X.trace • (1 : Algebra d) := by
  simp_rw [outer_sum_right]
  rw [← Finset.smul_sum, basis_pure_sum]

private lemma full_apply {d : ℕ}
    (e f : OrthonormalBasis (Fin d) ℂ (StateVector d)) (S T X : Algebra d) :
    ∑ i, ∑ j, (S * outerOperator (e i) (f j) * T) * X *
      (S * outerOperator (e i) (f j) * T)ᴴ =
      (T * X * Tᴴ).trace • (S * Sᴴ) := by
  have h := sum_sandwich S T X (fun z : Fin d × Fin d => outerOperator (e z.1) (f z.2))
  simpa [Fintype.sum_prod_type, two_basis_sandwich, Matrix.mul_smul, Matrix.smul_mul] using h

private lemma left_apply {d : ℕ}
    (e : OrthonormalBasis (Fin d) ℂ (StateVector d)) (S X : Algebra d) (w : StateVector d) :
    ∑ i, (S * outerOperator (e i) w) * X * (S * outerOperator (e i) w)ᴴ =
      (pureDensity w * X).trace • (S * Sᴴ) := by
  have h := sum_sandwich S 1 X (fun i => outerOperator (e i) w)
  simpa [outer_sum_left, Matrix.mul_smul, Matrix.smul_mul] using h

private lemma right_apply {d : ℕ}
    (f : OrthonormalBasis (Fin d) ℂ (StateVector d)) (T X : Algebra d) (v : StateVector d) :
    ∑ j, (outerOperator v (f j) * T) * X * (outerOperator v (f j) * T)ᴴ =
      (T * X * Tᴴ).trace • pureDensity v := by
  have h := sum_sandwich 1 T X (fun j => outerOperator v (f j))
  simpa [outer_sum_right] using h

private lemma full_norm {d : ℕ}
    (e f : OrthonormalBasis (Fin d) ℂ (StateVector d)) (S T : Algebra d) :
    ∑ i, ∑ j, (S * outerOperator (e i) (f j) * T)ᴴ *
      (S * outerOperator (e i) (f j) * T) =
      (Sᴴ * S).trace • (Tᴴ * T) := by
  have h := full_apply f e Tᴴ Sᴴ 1
  rw [Finset.sum_comm]
  simpa [Matrix.conjTranspose_mul, outer_star, Matrix.mul_assoc] using h

private lemma left_norm {d : ℕ}
    (e : OrthonormalBasis (Fin d) ℂ (StateVector d)) (S : Algebra d) (w : StateVector d) :
    ∑ i, (S * outerOperator (e i) w)ᴴ * (S * outerOperator (e i) w) =
      (Sᴴ * S).trace • pureDensity w := by
  have h := right_apply e Sᴴ 1 w
  simpa [Matrix.conjTranspose_mul, outer_star, Matrix.mul_assoc] using h

private lemma right_norm {d : ℕ}
    (f : OrthonormalBasis (Fin d) ℂ (StateVector d)) (T : Algebra d) (v : StateVector d) :
    ∑ j, (outerOperator v (f j) * T)ᴴ * (outerOperator v (f j) * T) =
      (pureDensity v).trace • (Tᴴ * T) := by
  have h := left_apply f Tᴴ 1 v
  simpa [Matrix.conjTranspose_mul, outer_star, Matrix.mul_assoc] using h

private lemma trace_pure {d : ℕ} (v : StateVector d) :
    (pureDensity v).trace = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  change (∑ i, v i * conj (v i)) = ((‖v‖ ^ 2 : ℝ) : ℂ)
  rw [EuclideanSpace.norm_sq_eq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

private lemma sqrt_trace {d : ℕ} (A X : Algebra d) (hA : A.PosSemidef) :
    (cfc Real.sqrt A * X * (cfc Real.sqrt A)ᴴ).trace = (A * X).trace := by
  rw [(sqrt_herm A).eq, Matrix.trace_mul_cycle, sqrt_sq A hA]

private lemma pure_trace_one {d : ℕ} (v : StateVector d) (hv : IsState v) :
    (pureDensity v).trace = 1 := by
  change ‖v‖ = 1 at hv
  rw [trace_pure, hv]
  norm_num

theorem solution (d : ℕ) (hd : 0 < d) :
    (∀ (m : ℕ) (R F : Fin m → Algebra d), (∀ k, IsDensityMatrix (R k)) →
      (∀ k, (F k).PosSemidef) →
      ∀ e f : OrthonormalBasis (Fin d) ℂ (StateVector d),
      (∀ X, krausApply (holevoKrausOperators R F e f) X = Entanglement.holevoMap R F X) ∧
      (IsPOVM F → IsKrausFamily (holevoKrausOperators R F e f))) ∧
    (∀ R : Fin d → Algebra d, (∀ k, IsDensityMatrix (R k)) →
      ∀ e f : OrthonormalBasis (Fin d) ℂ (StateVector d),
      (∀ X, krausApply (cqKrausOperators R e f) X =
        Entanglement.holevoMap R (fun k => pureDensity (f k)) X) ∧
      IsKrausFamily (cqKrausOperators R e f)) ∧
    (∀ F : Fin d → Algebra d, (∀ k, (F k).PosSemidef) →
      ∀ e f : OrthonormalBasis (Fin d) ℂ (StateVector d),
      (∀ X, krausApply (qcKrausOperators F e f) X =
        Entanglement.holevoMap (fun k => pureDensity (e k)) F X) ∧
      (IsPOVM F → IsKrausFamily (qcKrausOperators F e f))) ∧
    (∀ (e : OrthonormalBasis (Fin d) ℂ (StateVector d)) (psi : Fin d → StateVector d),
      (∀ k, IsState (psi k)) →
      (∀ X, krausApply (fun k => outerOperator (psi k) (e k)) X = pureCQEndomorphism e psi X) ∧
      IsKrausFamily (fun k => outerOperator (psi k) (e k))) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m R F hR hF e f
    constructor
    · intro X
      simp only [krausApply, holevoKrausOperators, Fintype.sum_prod_type,
        Entanglement.holevoMap, LinearMap.coe_mk, AddHom.coe_mk]
      apply Finset.sum_congr rfl
      intro k hk
      rw [full_apply, (sqrt_herm (R k)).eq, sqrt_sq _ (hR k).1,
        sqrt_trace _ _ (hF k)]
    · intro hPOVM
      unfold IsKrausFamily holevoKrausOperators
      simp only [Fintype.sum_prod_type]
      trans ∑ k, F k
      · apply Finset.sum_congr rfl
        intro k hk
        rw [full_norm, (sqrt_herm (R k)).eq, (sqrt_herm (F k)).eq,
          sqrt_sq _ (hR k).1, sqrt_sq _ (hF k), (hR k).2, one_smul]
      · exact hPOVM.2
  · intro R hR e f
    constructor
    · intro X
      simp only [krausApply, cqKrausOperators, Fintype.sum_prod_type,
        Entanglement.holevoMap, LinearMap.coe_mk, AddHom.coe_mk]
      apply Finset.sum_congr rfl
      intro k hk
      rw [left_apply, (sqrt_herm (R k)).eq, sqrt_sq _ (hR k).1]
    · unfold IsKrausFamily cqKrausOperators
      simp only [Fintype.sum_prod_type]
      trans ∑ k, pureDensity (f k)
      · apply Finset.sum_congr rfl
        intro k hk
        rw [left_norm, (sqrt_herm (R k)).eq, sqrt_sq _ (hR k).1,
          (hR k).2, one_smul]
      · exact basis_pure_sum f
  · intro F hF e f
    constructor
    · intro X
      simp only [krausApply, qcKrausOperators, Fintype.sum_prod_type,
        Entanglement.holevoMap, LinearMap.coe_mk, AddHom.coe_mk]
      apply Finset.sum_congr rfl
      intro k hk
      rw [right_apply, sqrt_trace _ _ (hF k)]
    · intro hPOVM
      unfold IsKrausFamily qcKrausOperators
      simp only [Fintype.sum_prod_type]
      trans ∑ k, F k
      · apply Finset.sum_congr rfl
        intro k hk
        rw [right_norm, (sqrt_herm (F k)).eq, sqrt_sq _ (hF k),
          pure_trace_one _ (basis_state e k), one_smul]
      · exact hPOVM.2
  · intro e psi hpsi
    constructor
    · intro X
      simp only [krausApply, outer_sandwich, pureCQEndomorphism,
        Entanglement.holevoMap, LinearMap.coe_mk, AddHom.coe_mk]
    · unfold IsKrausFamily
      trans ∑ k, pureDensity (e k)
      · apply Finset.sum_congr rfl
        intro k hk
        have h := outer_sandwich (e k) (psi k) 1
        simpa [outer_star, Matrix.mul_one, pure_trace_one _ (hpsi k)] using h
      · exact basis_pure_sum e

#print axioms solution
