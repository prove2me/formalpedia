-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P22.oddJointMoments
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T20:33:15.695922+00:00
-- url     : https://prove2.me/submissions/7fc0ecfb-b081-4680-adda-8831c7dfee1f

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

open scoped ComplexConjugate ComplexOrder Matrix Kronecker

noncomputable section

namespace X8P22
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22 Matrix


theorem x8_to_mul {I : Type} [Fintype I] [DecidableEq I] (M N : I → Op Bool) :
    tensorOps M * tensorOps N = tensorOps (fun i => M i * N i) := by
  ext a b
  simp only [tensorOps, mul_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.prod_mul_distrib]

theorem x8_to_one {I : Type} [Fintype I] [DecidableEq I] :
    tensorOps (fun _ : I => (1 : Op Bool)) = 1 := by
  ext a b
  simp only [tensorOps, one_apply]
  rw [Finset.prod_ite_zero]
  simp only [Finset.prod_const_one, Finset.mem_univ, true_implies]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg (fun h' => h (funext h')), if_neg h]

theorem x8_to_trace {I : Type} [Fintype I] [DecidableEq I] (M : I → Op Bool) :
    (tensorOps M).trace = ∏ i, (M i).trace := by
  simp only [trace, diag, tensorOps]
  rw [Fintype.prod_sum]

theorem x8_to_neg1 (x : Op Bool) :
    tensorOps (fun _ : Fin 1 => -x) = -tensorOps (fun _ : Fin 1 => x) := by
  ext a b
  simp [tensorOps]

theorem x8_to_H {I : Type} [Fintype I] (M : I → Op Bool) :
    (tensorOps M)ᴴ = tensorOps (fun i => (M i)ᴴ) := by
  ext a b
  simp [tensorOps, conjTranspose_apply]

/-- the sector tensor product. -/
def x8st {m k : ℕ} (M : Fin k → Op (Bool × Qubits m)) : Op (Qubits k × Signals m k) :=
  fun a b => ∏ j, M j (a.1 j, fun i => a.2 (j,i)) (b.1 j, fun i => b.2 (j,i))

def x8e (m k : ℕ) : (Qubits k × Signals m k) ≃ (Fin k → Bool × Qubits m) where
  toFun c j := (c.1 j, fun i => c.2 (j,i))
  invFun g := (fun j => (g j).1, fun w => (g w.1).2 w.2)
  left_inv c := by ext <;> simp
  right_inv g := by funext j; simp

theorem x8_st_mul {m k : ℕ} (M N : Fin k → Op (Bool × Qubits m)) :
    x8st M * x8st N = x8st (fun j => M j * N j) := by
  ext a b
  simp only [x8st, mul_apply]
  rw [Fintype.prod_sum, ← (x8e m k).sum_comp]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.prod_mul_distrib]
  rfl

theorem x8_st_H {m k : ℕ} (M : Fin k → Op (Bool × Qubits m)) :
    (x8st M)ᴴ = x8st (fun j => (M j)ᴴ) := by
  ext a b
  simp [x8st, conjTranspose_apply]

def x8sz {m k : ℕ} (z : Fin k → Op (Qubits m)) : Op (Signals m k) :=
  fun s s' => ∏ j, z j (fun i => s (j,i)) (fun i => s' (j,i))

theorem x8_st_kron {m k : ℕ} (y : Fin k → Op Bool) (z : Fin k → Op (Qubits m)) :
    x8st (fun j => y j ⊗ₖ z j) = tensorOps y ⊗ₖ x8sz z := by
  ext a b
  simp only [x8st, kroneckerMap_apply, tensorOps, x8sz, Finset.prod_mul_distrib]

theorem x8_sz_one {m k : ℕ} : x8sz (fun _ : Fin k => (1 : Op (Qubits m))) = 1 := by
  ext s s'
  simp only [x8sz, one_apply]
  rw [Finset.prod_ite_zero]
  simp only [Finset.prod_const_one, Finset.mem_univ, true_implies]
  by_cases h : s = s'
  · subst h; simp
  · rw [if_neg, if_neg h]
    intro h'
    apply h; funext w
    exact congrFun (h' w.1) w.2

/-- abstract conjugation by a quarter rotation. -/
theorem x8_c2 : (((Real.sqrt 2)⁻¹ : ℂ)) * (((Real.sqrt 2)⁻¹ : ℂ)) = 2⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  simp

theorem x8_qr_H {I : Type} [Fintype I] [DecidableEq I] (M : Op I) (hM : Mᴴ = M) :
    (quarterRotation M)ᴴ = ((Real.sqrt 2)⁻¹ : ℂ) • (1 + Complex.I • M) := by
  unfold quarterRotation
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hM]
  simp only [star_inv₀, RCLike.star_def, Complex.conj_ofReal, Complex.conj_I]
  rw [neg_smul, sub_neg_eq_add]

theorem x8_qr_conj {I : Type} [Fintype I] [DecidableEq I] (M A : Op I) (hM : Mᴴ = M) :
    (quarterRotation M)ᴴ * A * quarterRotation M =
      (2⁻¹ : ℂ) • (A + Complex.I • (M * A - A * M) + M * A * M) := by
  rw [x8_qr_H M hM]
  unfold quarterRotation
  rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, x8_c2]
  congr 1
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, smul_sub, smul_smul, Complex.I_mul_I]
  rw [smul_add, smul_smul, Complex.I_mul_I]
  module

theorem x8_qr_comm {I : Type} [Fintype I] [DecidableEq I] (M A : Op I) (hM : Mᴴ = M)
    (hMM : M * M = 1) (h : A * M = M * A) :
    (quarterRotation M)ᴴ * A * quarterRotation M = A := by
  rw [x8_qr_conj M A hM, h, sub_self, smul_zero, add_zero, ← h, Matrix.mul_assoc, hMM,
    Matrix.mul_one, ← two_smul ℂ A, smul_smul]
  norm_num

theorem x8_qr_anti {I : Type} [Fintype I] [DecidableEq I] (M A : Op I) (hM : Mᴴ = M)
    (hMM : M * M = 1) (h : A * M = -(M * A)) :
    (quarterRotation M)ᴴ * A * quarterRotation M = Complex.I • (M * A) := by
  rw [x8_qr_conj M A hM, Matrix.mul_assoc M A M, h, Matrix.mul_neg, ← Matrix.mul_assoc, hMM,
    Matrix.one_mul]
  rw [sub_neg_eq_add, ← two_smul ℂ (M * A), smul_smul]
  have : A + (Complex.I * 2) • (M * A) + -A = (Complex.I * 2) • (M * A) := by abel
  rw [this, smul_smul]
  congr 1
  ring


theorem x8_ax_H (P : Axis) : (axisMatrix P)ᴴ = axisMatrix P := by
  cases P <;> ext i j <;> cases i <;> cases j <;>
    simp [axisMatrix, pauliX, pauliY, pauliZ, conjTranspose_apply]

theorem x8_ax_sq (P : Axis) : axisMatrix P * axisMatrix P = 1 := by
  cases P <;> ext i j <;> cases i <;> cases j <;>
    simp [axisMatrix, pauliX, pauliY, pauliZ, mul_apply, Fintype.sum_bool]

theorem x8_ax_anti (P Q : Axis) (h : P ≠ Q) :
    axisMatrix P * axisMatrix Q = -(axisMatrix Q * axisMatrix P) := by
  cases P <;> cases Q <;> simp at h <;> ext i j <;> cases i <;> cases j <;>
    simp [axisMatrix, pauliX, pauliY, pauliZ, mul_apply, Fintype.sum_bool]

theorem x8_ax_tr (P Q : Axis) (h : P ≠ Q) : (axisMatrix P * axisMatrix Q).trace = 0 := by
  cases P <;> cases Q <;> simp at h <;>
    simp [axisMatrix, pauliX, pauliY, pauliZ, mul_apply, Fintype.sum_bool, trace]


theorem x8_kk (a b c d : Op Bool) : (a ⊗ₖ (tensorOps fun _ : Fin 1 => b)) * (c ⊗ₖ (tensorOps fun _ : Fin 1 => d)) = (a * c) ⊗ₖ (tensorOps fun _ : Fin 1 => b * d) := by
  rw [← mul_kronecker_mul, x8_to_mul]

theorem neg_kronecker {I J : Type} (a : Op I) (b : Op J) : (-a) ⊗ₖ b = -(a ⊗ₖ b) := by
  ext; simp

theorem kronecker_neg {I J : Type} (a : Op I) (b : Op J) : a ⊗ₖ (-b) = -(a ⊗ₖ b) := by
  ext; simp

theorem x8_M_H (P : Axis) : (axisMatrix P ⊗ₖ (tensorOps fun _ : Fin 1 => axisMatrix P))ᴴ =
    axisMatrix P ⊗ₖ (tensorOps fun _ : Fin 1 => axisMatrix P) := by
  rw [conjTranspose_kronecker, x8_to_H, x8_ax_H]

theorem x8_M_sq (P : Axis) : (axisMatrix P ⊗ₖ (tensorOps fun _ : Fin 1 => axisMatrix P)) *
    (axisMatrix P ⊗ₖ (tensorOps fun _ : Fin 1 => axisMatrix P)) = 1 := by
  rw [x8_kk, x8_ax_sq, x8_to_one, one_kronecker_one]

theorem x8_sector_one (P Q : Axis) :
    (sectorEncoder 1 P Q)ᴴ * 1 * sectorEncoder 1 P Q = 1 := by
  unfold sectorEncoder
  simp only [Matrix.kronecker]
  rw [conjTranspose_mul]
  have e : ∀ A B C D : Op (Bool × Qubits 1), A * B * 1 * (C * D) = A * (B * 1 * C) * D := by
    intro A B C D; simp only [Matrix.mul_assoc]
  rw [e, x8_qr_comm _ _ (x8_M_H P) (x8_M_sq P) (by simp), Matrix.mul_one,
    ← Matrix.mul_one (quarterRotation (axisMatrix Q ⊗ₖ (tensorOps fun _ : Fin 1 => axisMatrix Q)))ᴴ,
    x8_qr_comm _ _ (x8_M_H Q) (x8_M_sq Q) (by simp)]

theorem x8_sector (P Q : Axis) (h : P ≠ Q) :
    (sectorEncoder 1 P Q)ᴴ * (1 ⊗ₖ (tensorOps fun _ : Fin 1 => axisMatrix P * axisMatrix Q)) * sectorEncoder 1 P Q =
      (-(axisMatrix Q * axisMatrix P)) ⊗ₖ 1 := by
  unfold sectorEncoder
  simp only [Matrix.kronecker]
  rw [conjTranspose_mul]
  have e : ∀ A B C D E : Op (Bool × Qubits 1), A * B * E * (C * D) = A * (B * E * C) * D := by
    intro A B C D E; simp only [Matrix.mul_assoc]
  have hpq := x8_ax_anti P Q h
  have hp := x8_ax_sq P
  have hqp : axisMatrix Q * axisMatrix P = -(axisMatrix P * axisMatrix Q) := by rw [hpq, neg_neg]
  have hq := x8_ax_sq Q
  rw [e, x8_qr_anti _ _ (x8_M_H P) (x8_M_sq P)]
  · rw [x8_kk, Matrix.mul_one, ← Matrix.mul_assoc, hp, Matrix.one_mul]
    rw [x8_qr_anti _ _ (x8_M_H Q) (x8_M_sq Q)]
    · rw [Matrix.mul_smul, x8_kk, smul_smul, Complex.I_mul_I, hq, x8_to_one, neg_one_smul,
        neg_kronecker]
    · rw [Matrix.mul_smul, Matrix.smul_mul, x8_kk, x8_kk, hq, hpq, neg_kronecker, smul_neg]
  · rw [x8_kk, x8_kk, Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc, hp, Matrix.one_mul,
      Matrix.mul_assoc, hqp, Matrix.mul_neg, ← Matrix.mul_assoc, hp, Matrix.one_mul, x8_to_neg1,
      kronecker_neg]

end X8P22


open scoped ComplexConjugate ComplexOrder Matrix Kronecker

noncomputable section

namespace X8P22
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22 Matrix

def x8σ (k : ℕ) : Qubits k ≃ Signals 1 k where
  toFun b w := b w.1
  invFun s j := s (j, 0)
  left_inv b := rfl
  right_inv s := by
    funext w
    show s (w.1, 0) = s w
    exact congrArg s (Prod.ext rfl (Subsingleton.elim _ _))

theorem x8_join (k : ℕ) (b : Qubits k) (t : Rest 1 k 0) : joinSignal 0 b t = x8σ k b := by
  funext w
  simp [joinSignal, x8σ, Subsingleton.elim w.2 0]

theorem x8_rest_card (k : ℕ) : Fintype.card (Rest 1 k 0) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨fun w => False.elim (w.2 (Subsingleton.elim _ _)), fun t => ?_⟩
  funext w; exact False.elim (w.2 (Subsingleton.elim _ _))

theorem x8_indiv (k : ℕ) (R : EuclideanSpace ℂ (Signals 1 k × Signals 1 k))
    (U : Op (Qubits k × Signals 1 k)) (X : Op (Qubits k)) (b b' : Qubits k) :
    individual R U 0 X b b' =
      ∑ a, (U * (X ⊗ₖ rhoS R) * Uᴴ) (a, x8σ k b) (a, x8σ k b') := by
  simp only [individual, traceRight, authorized, Matrix.of_apply, x8_join, Finset.sum_const,
    Finset.card_univ, x8_rest_card, one_smul]
  simp only [encoded, encoding, rhoS, traceRight, pureDensity, Matrix.mul_apply,
    Matrix.conjTranspose_apply, kroneckerMap_apply, Matrix.of_apply, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum, star_sum, star_mul']
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [RCLike.star_def]
  ring


theorem x8_T0 (k : ℕ) (G : (Qubits k × Signals 1 k) → (Qubits k × Signals 1 k) → ℂ)
    (O : Signals 1 k → Signals 1 k → ℂ) :
    ∑ b, ∑ b', (∑ a, G (a, x8σ k b) (a, x8σ k b')) * O (x8σ k b') (x8σ k b) =
      (Matrix.of G * ((1 : Matrix (Qubits k) (Qubits k) ℂ) ⊗ₖ Matrix.of O)).trace := by
  simp only [Finset.sum_mul]
  rw [Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, kroneckerMap_apply, Matrix.one_apply, Matrix.of_apply,
    Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
  conv_rhs => arg 2; ext a; arg 2; ext s; rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← (x8σ k).sum_comp]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← (x8σ k).sum_comp]

theorem x8_T (k : ℕ) (R : EuclideanSpace ℂ (Signals 1 k × Signals 1 k))
    (U : Op (Qubits k × Signals 1 k)) (X : Op (Qubits k)) (O : Op (Signals 1 k)) :
    ∑ b, ∑ b', individual R U 0 X b b' * O (x8σ k b') (x8σ k b) =
      (U * (X ⊗ₖ rhoS R) * Uᴴ * ((1 : Op (Qubits k)) ⊗ₖ O)).trace := by
  simp only [x8_indiv]
  exact x8_T0 k _ O

theorem x8_trρ (k : ℕ) (R : EuclideanSpace ℂ (Signals 1 k × Signals 1 k)) (hR : IsState R) :
    (rhoS R).trace = 1 := by
  have h1 : ∑ i, ‖R i‖ ^ 2 = 1 := by
    have := EuclideanSpace.norm_eq R
    rw [hR] at this
    have h2 := congrArg (· ^ 2) this
    simp only [one_pow] at h2
    rw [h2, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  simp only [rhoS, traceRight, pureDensity, Matrix.trace, Matrix.diag, Matrix.of_apply]
  rw [← Fintype.sum_prod_type']
  have : ∀ i : Signals 1 k × Signals 1 k, R i * conj (R i) = ((‖R i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [this]
  rw [← Complex.ofReal_sum, h1, Complex.ofReal_one]

theorem x8_main (k : ℕ) (hk : 1 ≤ k) (P Q : Axis) (hPQ : P ≠ Q)
    (R : EuclideanSpace ℂ (Signals 1 k × Signals 1 k)) (hR : IsState R) :
    ¬ Concealed R (twoPauliEncoder 1 k P Q) 0 := by
  rintro ⟨τ, -, hτ⟩
  set j0 : Fin k := ⟨0, hk⟩
  set U := twoPauliEncoder 1 k P Q with hU
  have hUst : U = x8st (fun _ => sectorEncoder 1 P Q) := rfl
  let x : Fin k → Op Bool := fun j => if j = j0 then axisMatrix P * axisMatrix Q else 1
  let z : Fin k → Op (Qubits 1) := fun j =>
    if j = j0 then (tensorOps fun _ : Fin 1 => axisMatrix P * axisMatrix Q) else 1
  let y : Fin k → Op Bool := fun j => if j = j0 then -(axisMatrix Q * axisMatrix P) else 1
  have h0 : individual R U 0 (tensorOps x) = 0 := by
    rw [hτ, x8_to_trace, Finset.prod_eq_zero (Finset.mem_univ j0), zero_smul]
    simp only [x, if_pos rfl]
    exact x8_ax_tr P Q hPQ
  have hT := x8_T k R U (tensorOps x) (x8sz z)
  simp only [h0, Matrix.zero_apply, zero_mul, Finset.sum_const_zero] at hT
  have hconj : Uᴴ * ((1 : Op (Qubits k)) ⊗ₖ x8sz z) * U = tensorOps y ⊗ₖ 1 := by
    rw [← x8_to_one, ← x8_st_kron, hUst, x8_st_H, x8_st_mul, x8_st_mul, ← x8_sz_one (m := 1),
      ← x8_st_kron]
    congr 1
    funext j
    by_cases hj : j = j0
    · simp only [z, y, if_pos hj]
      exact x8_sector P Q hPQ
    · simp only [z, y, if_neg hj]
      rw [one_kronecker_one, x8_sector_one]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hconj,
    ← mul_kronecker_mul, Matrix.trace_kronecker, Matrix.mul_one, x8_trρ k R hR, mul_one,
    x8_to_mul, x8_to_trace] at hT
  rw [eq_comm, Finset.prod_eq_zero_iff] at hT
  obtain ⟨j, -, hj⟩ := hT
  by_cases h : j = j0
  · simp only [x, y, if_pos h] at hj
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.mul_assoc (axisMatrix P), x8_ax_sq,
      Matrix.mul_one, x8_ax_sq, Matrix.trace_neg, Matrix.trace_one] at hj
    norm_num at hj
  · simp only [x, y, if_neg h, Matrix.mul_one, Matrix.trace_one] at hj
    norm_num at hj

end X8P22


open scoped ComplexConjugate ComplexOrder Matrix Kronecker

noncomputable section

namespace X8P22
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22 Matrix

theorem x8_to_smul {m : ℕ} (c : ℂ) (x : Op Bool) :
    tensorOps (fun _ : Fin m => c • x) = c ^ m • tensorOps (fun _ : Fin m => x) := by
  ext a b
  simp [tensorOps, Finset.prod_mul_distrib, Finset.prod_const]

theorem x8_to_negm {m : ℕ} (hm : Odd m) (x : Op Bool) :
    tensorOps (fun _ : Fin m => -x) = -tensorOps (fun _ : Fin m => x) := by
  rw [← neg_one_smul ℂ x, x8_to_smul, hm.neg_one_pow, neg_one_smul]

theorem x8_kkm {m : ℕ} (a b c d : Op Bool) :
    (a ⊗ₖ (tensorOps fun _ : Fin m => b)) * (c ⊗ₖ (tensorOps fun _ : Fin m => d)) =
      (a * c) ⊗ₖ (tensorOps fun _ : Fin m => b * d) := by
  rw [← mul_kronecker_mul, x8_to_mul]

theorem x8_MH {m : ℕ} (P : Axis) : (axisMatrix P ⊗ₖ (tensorOps fun _ : Fin m => axisMatrix P))ᴴ =
    axisMatrix P ⊗ₖ (tensorOps fun _ : Fin m => axisMatrix P) := by
  rw [conjTranspose_kronecker, x8_to_H, x8_ax_H]

theorem x8_Msq {m : ℕ} (P : Axis) : (axisMatrix P ⊗ₖ (tensorOps fun _ : Fin m => axisMatrix P)) *
    (axisMatrix P ⊗ₖ (tensorOps fun _ : Fin m => axisMatrix P)) = 1 := by
  rw [x8_kkm, x8_ax_sq, x8_to_one, one_kronecker_one]

theorem x8_sector_onem (m : ℕ) (P Q : Axis) :
    (sectorEncoder m P Q)ᴴ * 1 * sectorEncoder m P Q = 1 := by
  unfold sectorEncoder
  simp only [Matrix.kronecker]
  rw [conjTranspose_mul]
  have e : ∀ A B C D : Op (Bool × Qubits m), A * B * 1 * (C * D) = A * (B * 1 * C) * D := by
    intro A B C D; simp only [Matrix.mul_assoc]
  rw [e, x8_qr_comm _ _ (x8_MH P) (x8_Msq P) (by simp), Matrix.mul_one,
    ← Matrix.mul_one (quarterRotation (axisMatrix Q ⊗ₖ (tensorOps fun _ : Fin m => axisMatrix Q)))ᴴ,
    x8_qr_comm _ _ (x8_MH Q) (x8_Msq Q) (by simp)]

theorem x8_Ipow (t : ℕ) : Complex.I ^ (2 * t + 1) = (-1) ^ t * Complex.I := by
  rw [pow_succ, pow_mul, Complex.I_sq]

theorem x8_sectorm (m : ℕ) (hodd : Odd m) (P Q : Axis) (h : P ≠ Q) :
    (sectorEncoder m P Q)ᴴ * (1 ⊗ₖ (tensorOps fun _ : Fin m => remaining P Q)) *
      sectorEncoder m P Q = ((-1 : ℂ) ^ ((m - 1) / 2)) • (remaining P Q ⊗ₖ 1) := by
  obtain ⟨t, rfl⟩ := hodd
  have ht : (2 * t + 1 - 1) / 2 = t := by omega
  rw [ht]
  unfold sectorEncoder remaining
  simp only [Matrix.kronecker]
  rw [conjTranspose_mul]
  have e : ∀ A B C D E : Op (Bool × Qubits (2 * t + 1)),
      A * B * E * (C * D) = A * (B * E * C) * D := by
    intro A B C D E; simp only [Matrix.mul_assoc]
  have hpq := x8_ax_anti P Q h
  have hp := x8_ax_sq P
  have hqp : axisMatrix Q * axisMatrix P = -(axisMatrix P * axisMatrix Q) := by rw [hpq, neg_neg]
  have hq := x8_ax_sq Q
  -- P * R = I • Q and R * P = -(I • Q), where R = I • (P * Q)
  have hPR : axisMatrix P * (Complex.I • (axisMatrix P * axisMatrix Q)) = Complex.I • axisMatrix Q := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, hp, Matrix.one_mul]
  have hRP : (Complex.I • (axisMatrix P * axisMatrix Q)) * axisMatrix P = -(Complex.I • axisMatrix Q) := by
    rw [Matrix.smul_mul, Matrix.mul_assoc, hqp, Matrix.mul_neg, ← Matrix.mul_assoc, hp,
      Matrix.one_mul, smul_neg]
  rw [e, x8_qr_anti _ _ (x8_MH P) (x8_Msq P)]
  · rw [x8_kkm, Matrix.mul_one, hPR, x8_to_smul, kronecker_smul]
    rw [x8_qr_anti _ _ (x8_MH Q) (x8_Msq Q)]
    · rw [Matrix.mul_smul, Matrix.mul_smul, x8_kkm, hq, x8_to_one, smul_smul, x8_Ipow,
        Matrix.smul_kronecker, smul_smul, hqp, neg_kronecker, smul_neg, ← neg_smul, smul_smul]
      congr 1
      linear_combination (-(-1 : ℂ) ^ t * Complex.I) * Complex.I_sq
    · simp only [Matrix.smul_mul, Matrix.mul_smul]
      rw [x8_kkm, x8_kkm, hq, hpq, neg_kronecker, smul_neg, smul_neg]
  · rw [x8_kkm, x8_kkm, Matrix.one_mul, Matrix.mul_one, hPR, hRP,
      x8_to_negm ⟨t, rfl⟩, kronecker_neg]


theorem x8_SM (m k : ℕ) (P Q : Axis) (c : Qubits k) :
    sectorMoment m k P Q c =
      x8sz (fun j => tensorOps fun _ : Fin m => if c j then remaining P Q else 1) := by
  ext s s'
  simp only [sectorMoment, x8sz, tensorOps]
  rw [Fintype.prod_prod_type]

theorem x8_to_ite (k : ℕ) (c : Qubits k) (s : ℂ) (R : Op Bool) :
    tensorOps (fun j => if c j then s • R else 1) =
      s ^ hammingWeight c • tensorOps (fun j => if c j then R else 1) := by
  ext a b
  simp only [tensorOps, Matrix.smul_apply, smul_eq_mul, hammingWeight]
  have : ∀ j, (if c j then s • R else 1) (a j) (b j) =
      (if c j then s else 1) * (if c j then R else 1) (a j) (b j) := by
    intro j; by_cases hc : c j = true <;> simp [hc]
  simp only [this, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

theorem x8_moment (m k : ℕ) (hodd : Odd m) (P Q : Axis) (h : P ≠ Q) (c : Qubits k) :
    (twoPauliEncoder m k P Q)ᴴ * ((1 : Op (Qubits k)) ⊗ₖ sectorMoment m k P Q c) *
      twoPauliEncoder m k P Q = ((-1 : ℂ) ^ ((m - 1) / 2)) ^ (hammingWeight c) •
        (inputMoment k P Q c ⊗ₖ (1 : Op (Signals m k))) := by
  have hUst : twoPauliEncoder m k P Q = x8st (fun _ => sectorEncoder m P Q) := rfl
  rw [x8_SM, ← x8_to_one, ← x8_st_kron, hUst, x8_st_H, x8_st_mul, x8_st_mul]
  have : (fun j => (sectorEncoder m P Q)ᴴ * ((1 : Op Bool) ⊗ₖ
      (tensorOps fun _ : Fin m => if c j then remaining P Q else 1)) * sectorEncoder m P Q) =
      fun j => (if c j then ((-1 : ℂ) ^ ((m - 1) / 2)) • remaining P Q else 1) ⊗ₖ
        (1 : Op (Qubits m)) := by
    funext j
    by_cases hc : c j = true
    · simp only [hc, if_true]
      rw [x8_sectorm m hodd P Q h, Matrix.smul_kronecker]
    · simp only [hc, if_false, Bool.false_eq_true]
      rw [x8_to_one, one_kronecker_one, x8_sector_onem]
  rw [this, x8_st_kron, x8_sz_one, x8_to_ite, Matrix.smul_kronecker]
  rfl

theorem x8_joint (m k : ℕ) (R : EuclideanSpace ℂ (Signals m k × Signals m k))
    (U : Op (Qubits k × Signals m k)) (X : Op (Qubits k)) (s s' : Signals m k) :
    jointSignals R U X s s' = ∑ a, (U * (X ⊗ₖ rhoS R) * Uᴴ) (a, s) (a, s') := by
  simp only [jointSignals, traceLeft, traceRight, Matrix.of_apply]
  simp only [encoded, encoding, rhoS, traceRight, pureDensity, Matrix.mul_apply,
    Matrix.conjTranspose_apply, kroneckerMap_apply, Matrix.of_apply, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum, star_sum, star_mul']
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s'' _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s3 _ => ?_
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [RCLike.star_def]
  ring


theorem x8_T1 (m k : ℕ) (G : (Qubits k × Signals m k) → (Qubits k × Signals m k) → ℂ)
    (O : Signals m k → Signals m k → ℂ) :
    ∑ s, ∑ s', O s s' * (∑ a, G (a, s') (a, s)) =
      (Matrix.of G * ((1 : Matrix (Qubits k) (Qubits k) ℂ) ⊗ₖ Matrix.of O)).trace := by
  simp only [Finset.mul_sum]
  rw [Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, kroneckerMap_apply, Matrix.one_apply, Matrix.of_apply,
    Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
  conv_rhs => arg 2; ext a; arg 2; ext s; rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun b' _ => ?_
  ring

theorem x8_trρm (m k : ℕ) (R : EuclideanSpace ℂ (Signals m k × Signals m k)) (hR : IsState R) :
    (rhoS R).trace = 1 := by
  have h1 : ∑ i, ‖R i‖ ^ 2 = 1 := by
    have := EuclideanSpace.norm_eq R
    rw [hR] at this
    have h2 := congrArg (· ^ 2) this
    simp only [one_pow] at h2
    rw [h2, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  simp only [rhoS, traceRight, pureDensity, Matrix.trace, Matrix.diag, Matrix.of_apply]
  rw [← Fintype.sum_prod_type']
  have : ∀ i : Signals m k × Signals m k, R i * conj (R i) = ((‖R i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [this]
  rw [← Complex.ofReal_sum, h1, Complex.ofReal_one]

theorem x8_part2 (m k : ℕ) (hodd : Odd m) (P Q : Axis) (h : P ≠ Q)
    (R : EuclideanSpace ℂ (Signals m k × Signals m k)) (hR : IsState R) (c : Qubits k)
    (rho : Op (Qubits k)) :
    (sectorMoment m k P Q c * jointSignals R (twoPauliEncoder m k P Q) rho).trace =
      ((-1 : ℂ) ^ ((m - 1) / 2)) ^ (hammingWeight c) * (inputMoment k P Q c * rho).trace := by
  set U := twoPauliEncoder m k P Q
  have e1 : (sectorMoment m k P Q c * jointSignals R U rho).trace =
      ∑ s, ∑ s', sectorMoment m k P Q c s s' *
        (∑ a, (U * (rho ⊗ₖ rhoS R) * Uᴴ) (a, s') (a, s)) := by
    rw [Matrix.trace]
    simp only [Matrix.diag, Matrix.mul_apply, x8_joint]
  rw [e1, x8_T1 m k (fun z z' => (U * (rho ⊗ₖ rhoS R) * Uᴴ) z z')
    (fun s s' => sectorMoment m k P Q c s s')]
  change (U * (rho ⊗ₖ rhoS R) * Uᴴ * ((1 : Op (Qubits k)) ⊗ₖ sectorMoment m k P Q c)).trace = _
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
    x8_moment m k hodd P Q h c, Matrix.mul_smul, Matrix.trace_smul, ← mul_kronecker_mul,
    Matrix.trace_kronecker, Matrix.mul_one, x8_trρm m k R hR, mul_one, Matrix.trace_mul_comm,
    smul_eq_mul]

end X8P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Eqs.(S12)–(S13), PDF pp.23–24 and main p.4. Includes c=0 and m=1. -/
theorem x8_target (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) (hodd : Odd m)
    (P Q : Axis) (hPQ : P ≠ Q)
    (R : EuclideanSpace ℂ (Signals m k × Signals m k)) (hR : IsState R) (c : Qubits k) :
    (twoPauliEncoder m k P Q)ᴴ * Matrix.kronecker (1 : Op (Qubits k)) (sectorMoment m k P Q c) *
      twoPauliEncoder m k P Q = ((-1 : ℂ)^((m-1)/2))^(hammingWeight c) •
        Matrix.kronecker (inputMoment k P Q c) (1 : Op (Signals m k)) ∧
    ∀ rho : Op (Qubits k), IsDensityMatrix rho →
      (sectorMoment m k P Q c * jointSignals R (twoPauliEncoder m k P Q) rho).trace =
        ((-1 : ℂ)^((m-1)/2))^(hammingWeight c) * (inputMoment k P Q c * rho).trace := by
  refine ⟨?_, fun rho _ => X8P22.x8_part2 m k hodd P Q hPQ R hR c rho⟩
  simp only [Matrix.kronecker]
  convert X8P22.x8_moment m k hodd P Q hPQ c using 3

end

end QAlgorithms.Papers.Independent.Information100.P22

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22 in
/-- Eqs.(S12)–(S13), PDF pp.23–24 and main p.4. Includes c=0 and m=1. -/
theorem solution (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) (hodd : Odd m)
    (P Q : Axis) (hPQ : P ≠ Q)
    (R : EuclideanSpace ℂ (Signals m k × Signals m k)) (hR : IsState R) (c : Qubits k) :
    (twoPauliEncoder m k P Q)ᴴ * Matrix.kronecker (1 : Op (Qubits k)) (sectorMoment m k P Q c) *
      twoPauliEncoder m k P Q = ((-1 : ℂ)^((m-1)/2))^(hammingWeight c) •
        Matrix.kronecker (inputMoment k P Q c) (1 : Op (Signals m k)) ∧
    ∀ rho : Op (Qubits k), IsDensityMatrix rho →
      (sectorMoment m k P Q c * jointSignals R (twoPauliEncoder m k P Q) rho).trace =
        ((-1 : ℂ)^((m-1)/2))^(hammingWeight c) * (inputMoment k P Q c * rho).trace :=
  x8_target m k hm hk hodd P Q hPQ R hR c
