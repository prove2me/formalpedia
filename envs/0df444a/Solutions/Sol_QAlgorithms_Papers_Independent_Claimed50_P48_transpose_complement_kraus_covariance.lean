-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P48.transpose_complement_kraus_covariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:30:36.340319+00:00
-- url     : https://prove2.me/submissions/887a3622-8328-43de-a0f1-228dce13e7d9

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

theorem g68l_c_sq (d : ℕ) (hd : 2 ≤ d) :
    ((Real.sqrt (2 * ((d : ℝ) - 1)))⁻¹ : ℂ) * ((Real.sqrt (2 * ((d : ℝ) - 1)))⁻¹ : ℂ) =
      (2 * ((d : ℂ) - 1))⁻¹ := by
  have h1 : (0 : ℝ) ≤ 2 * ((d : ℝ) - 1) := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt h1]
  push_cast; ring

theorem g68l_rows_eq (d : ℕ) (j : Fin d) :
    antisymmetricRows d j = ((Real.sqrt (2 * ((d : ℝ) - 1)))⁻¹ : ℂ) •
      ((1 - environmentSwap (E := Fin d)) * Matrix.of (fun (p : Fin d × Fin d) (i : Fin d) =>
        if p.1 = i ∧ p.2 = j then (1 : ℂ) else 0)) := by
  ext p i
  simp only [antisymmetricRows, Matrix.smul_apply, smul_eq_mul, Matrix.sub_mul, Matrix.one_mul,
    Matrix.sub_apply, Matrix.of_apply, Matrix.mul_apply, environmentSwap]
  congr 2
  rw [Finset.sum_eq_single (p.2, p.1)]
  · simp [and_comm]
  · intro q _ hq
    have : ¬ p = (q.2, q.1) := fun h => hq (by rw [h])
    simp [this]
  · simp

theorem g68l_swap_herm (d : ℕ) : (1 - environmentSwap (E := Fin d))ᴴ = 1 - environmentSwap (E := Fin d) := by
  have hF : (environmentSwap (E := Fin d))ᴴ = environmentSwap (E := Fin d) := by
    ext ⟨a, b⟩ ⟨c, e⟩
    simp only [Matrix.conjTranspose_apply, environmentSwap, Prod.mk.injEq]
    by_cases h : c = b ∧ e = a
    · rw [if_pos h, if_pos ⟨h.2.symm, h.1.symm⟩]; simp
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.2.symm, h'.1.symm⟩)]; simp
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hF]

theorem g68l_M_sum (d : ℕ) (rho : Matrix (Fin d) (Fin d) ℂ) :
    ∑ j : Fin d, Matrix.of (fun (p : Fin d × Fin d) (i : Fin d) => if p.1 = i ∧ p.2 = j then (1 : ℂ) else 0) *
      rho * (Matrix.of (fun (p : Fin d × Fin d) (i : Fin d) => if p.1 = i ∧ p.2 = j then (1 : ℂ) else 0))ᴴ =
      rho ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext p q
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, ite_and]
  rw [Finset.sum_eq_single q.1 (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  by_cases h : q.2 = p.2
  · simp [h]
  · simp [h, Ne.symm h]

theorem g68l_part1 (d : ℕ) (hd : 2 ≤ d) : antisymmetricComplement d = krausApply (antisymmetricRows d) := by
  funext rho
  simp only [krausApply, g68l_rows_eq]
  set c : ℂ := ((Real.sqrt (2 * ((d : ℝ) - 1)))⁻¹ : ℂ) with hc
  set G := (1 - environmentSwap (E := Fin d))
  have hstar : star c = c := by simp [hc, Complex.conj_ofReal]
  have : ∀ j : Fin d, (c • (G * Matrix.of (fun (p : Fin d × Fin d) (i : Fin d) =>
        if p.1 = i ∧ p.2 = j then (1 : ℂ) else 0))) * rho *
      (c • (G * Matrix.of (fun (p : Fin d × Fin d) (i : Fin d) =>
        if p.1 = i ∧ p.2 = j then (1 : ℂ) else 0)))ᴴ =
      (c * c) • (G * (Matrix.of (fun (p : Fin d × Fin d) (i : Fin d) =>
        if p.1 = i ∧ p.2 = j then (1 : ℂ) else 0) * rho * (Matrix.of (fun (p : Fin d × Fin d) (i : Fin d) =>
        if p.1 = i ∧ p.2 = j then (1 : ℂ) else 0))ᴴ) * G) := by
    intro j
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, g68l_swap_herm, hstar]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    rfl
  rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.smul_sum, ← Finset.sum_mul, ← Finset.mul_sum,
    g68l_M_sum, hc, g68l_c_sq d hd]
  rfl

theorem g68l_part2 (d : ℕ) (j : Fin d) (psi : EuclideanSpace ℂ (Fin d)) (ab : Fin d × Fin d) :
    Matrix.mulVec (antisymmetricRows d j) (fun i => psi i) ab =
        ((Real.sqrt (2 * ((d : ℝ) - 1)))⁻¹ : ℂ) *
          (psi ab.1 * (ket j) ab.2 - (ket j) ab.1 * psi ab.2) := by
  simp only [Matrix.mulVec, dotProduct, antisymmetricRows, ket, mul_sub, sub_mul, Finset.sum_sub_distrib,
    ite_and, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, EuclideanSpace.single_apply]
  by_cases h1 : ab.2 = j <;> by_cases h2 : ab.1 = j <;> simp [h1, h2, eq_comm]

theorem g68l_swap_comm (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) :
    environmentSwap (E := Fin d) * (U ⊗ₖ U) = (U ⊗ₖ U) * environmentSwap (E := Fin d) := by
  ext p q
  simp only [Matrix.mul_apply, environmentSwap, Matrix.kroneckerMap_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (p.2, p.1), Finset.sum_eq_single (q.2, q.1)]
  · simp [mul_comm]
  · intro x _ hx; rw [if_neg]; intro h; apply hx; rw [h]
  · simp
  · intro x _ hx; rw [if_neg]; intro h; apply hx; rw [h]
  · simp

theorem g68l_part3 (d : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) (rho : Matrix (Fin d) (Fin d) ℂ) :
    antisymmetricComplement d ((U : Matrix (Fin d) (Fin d) ℂ) * rho * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
        ((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ)) *
          antisymmetricComplement d rho *
          ((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ))ᴴ := by
  set V : Matrix (Fin d) (Fin d) ℂ := (U : Matrix (Fin d) (Fin d) ℂ)
  have hU : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  have hk : (V * rho * Vᴴ) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ) = (V ⊗ₖ V) * (rho ⊗ₖ 1) * (V ⊗ₖ V)ᴴ := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, hU]
  have hG : (1 - environmentSwap (E := Fin d)) * (V ⊗ₖ V) = (V ⊗ₖ V) * (1 - environmentSwap (E := Fin d)) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, g68l_swap_comm]
  have hG' : (V ⊗ₖ V)ᴴ * (1 - environmentSwap (E := Fin d)) = (1 - environmentSwap (E := Fin d)) * (V ⊗ₖ V)ᴴ := by
    have := congrArg Matrix.conjTranspose hG
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, g68l_swap_herm] at this
    exact this
  simp only [antisymmetricComplement, hk, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [← Matrix.mul_assoc, hG]
  simp only [Matrix.mul_assoc, hG']

theorem g68l_part4 (d : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) (rho : Matrix (Fin d) (Fin d) ℂ) :
      wernerHolevo d ((U : Matrix (Fin d) (Fin d) ℂ) * rho * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
        (U : Matrix (Fin d) (Fin d) ℂ).map conj * wernerHolevo d rho *
          ((U : Matrix (Fin d) (Fin d) ℂ).map conj)ᴴ := by
  set V : Matrix (Fin d) (Fin d) ℂ := (U : Matrix (Fin d) (Fin d) ℂ)
  have hU : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  have hU' : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have h1 : (V.map conj)ᴴ = Vᵀ := by ext i j; simp [Matrix.conjTranspose_apply]
  have h2 : (Vᴴ)ᵀ = V.map conj := by ext i j; simp [Matrix.conjTranspose_apply]
  have h3 : V.map conj * Vᵀ = 1 := by
    rw [← h2, ← Matrix.transpose_mul, hU, Matrix.transpose_one]
  have htr : (V * rho * Vᴴ).trace = rho.trace := by
    rw [Matrix.trace_mul_cycle, hU', Matrix.one_mul]
  simp only [wernerHolevo]
  rw [htr]
  simp only [h1, Matrix.transpose_mul, h2, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h3, Matrix.mul_assoc]

/-- PDF pp.7–8: d Kraus maps into d^2 dimensions, all-operator equality,
receiver covariance with conjugate U, and complement covariance with U tensor U. -/
theorem solution (d : ℕ) (hd : 2 ≤ d) :
    antisymmetricComplement d = krausApply (antisymmetricRows d) ∧
    (∀ (j : Fin d) (psi : EuclideanSpace ℂ (Fin d)) (ab : Fin d × Fin d),
      Matrix.mulVec (antisymmetricRows d j) (fun i => psi i) ab =
        ((Real.sqrt (2 * ((d : ℝ) - 1)))⁻¹ : ℂ) *
          (psi ab.1 * (ket j) ab.2 - (ket j) ab.1 * psi ab.2)) ∧
    (∀ (U : Matrix.unitaryGroup (Fin d) ℂ) rho,
      antisymmetricComplement d ((U : Matrix (Fin d) (Fin d) ℂ) * rho * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
        ((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ)) *
          antisymmetricComplement d rho *
          ((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ))ᴴ) ∧
    (∀ (U : Matrix.unitaryGroup (Fin d) ℂ) rho,
      wernerHolevo d ((U : Matrix (Fin d) (Fin d) ℂ) * rho * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
        (U : Matrix (Fin d) (Fin d) ℂ).map conj * wernerHolevo d rho *
          ((U : Matrix (Fin d) (Fin d) ℂ).map conj)ᴴ) := by
  exact ⟨g68l_part1 d hd, g68l_part2 d, g68l_part3 d, g68l_part4 d⟩



end
