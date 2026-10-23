-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P22.exceptionalKernelStructure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T21:03:11.098336+00:00
-- url     : https://prove2.me/submissions/390a168e-ad72-4a89-b48e-e8bb70c1689c

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

/-- group law of Pauli labels, ignoring phases. -/
def mulO : Option Axis → Option Axis → Option Axis
  | none, y => y
  | some a, none => some a
  | some a, some b => if a = b then none else some (remainingAxis a b)

/-- anticommutation of Pauli labels. -/
def antiO : Option Axis → Option Axis → Bool
  | some a, some b => decide (a ≠ b)
  | _, _ => false

/-- phase of a product of Pauli labels. -/
def phO : Option Axis → Option Axis → ℂ
  | some .X, some .Y => Complex.I
  | some .Y, some .X => -Complex.I
  | some .Y, some .Z => Complex.I
  | some .Z, some .Y => -Complex.I
  | some .Z, some .X => Complex.I
  | some .X, some .Z => -Complex.I
  | _, _ => 1

theorem x8_phO_ne (x y : Option Axis) : phO x y ≠ 0 := by
  rcases x with _ | x <;> rcases y with _ | y
  · simp [phO]
  · simp [phO]
  · cases x <;> simp [phO]
  · cases x <;> cases y <;> simp [phO]

theorem x8_dm_comm (x y : Option Axis) :
    directionMatrix x * directionMatrix y =
      (if antiO x y then (-1 : ℂ) else 1) • (directionMatrix y * directionMatrix x) := by
  rcases x with _ | x <;> rcases y with _ | y
  · simp [antiO, directionMatrix]
  · simp [antiO, directionMatrix]
  · simp [antiO, directionMatrix]
  · cases x <;> cases y <;> ext i j <;> cases i <;> cases j <;>
      simp [antiO, directionMatrix, axisMatrix, pauliX, pauliY, pauliZ, mul_apply, Fintype.sum_bool]

theorem x8_dm_mul (x y : Option Axis) :
    directionMatrix x * directionMatrix y = phO x y • directionMatrix (mulO x y) := by
  rcases x with _ | x <;> rcases y with _ | y
  · simp [phO, mulO, directionMatrix]
  · simp [phO, mulO, directionMatrix]
  · simp [phO, mulO, directionMatrix]
  · cases x <;> cases y <;> ext i j <;> cases i <;> cases j <;>
      simp [phO, mulO, remainingAxis, directionMatrix, axisMatrix, pauliX, pauliY, pauliZ,
        mul_apply, Fintype.sum_bool]

theorem x8_dm_sq (x : Option Axis) : directionMatrix x * directionMatrix x = 1 := by
  rcases x with _ | x
  · simp [directionMatrix]
  · exact x8_ax_sq x

theorem x8_dm_H (x : Option Axis) : (directionMatrix x)ᴴ = directionMatrix x := by
  rcases x with _ | x
  · simp [directionMatrix]
  · exact x8_ax_H x

theorem x8_to_smulf {I : Type} [Fintype I] (c : I → ℂ) (M : I → Op Bool) :
    tensorOps (fun i => c i • M i) = (∏ i, c i) • tensorOps M := by
  ext a b
  simp [tensorOps, Finset.prod_mul_distrib]

/-- Pauli word on source and m signals. -/
def x8K {m : ℕ} (a : Option Axis) (f : Fin m → Option Axis) : Op (Bool × Qubits m) :=
  directionMatrix a ⊗ₖ tensorOps (fun i => directionMatrix (f i))

theorem x8_K_mul {m : ℕ} (a b : Option Axis) (f g : Fin m → Option Axis) :
    x8K a f * x8K b g = (phO a b * ∏ i, phO (f i) (g i)) •
      x8K (mulO a b) (fun i => mulO (f i) (g i)) := by
  unfold x8K
  rw [← mul_kronecker_mul, x8_to_mul]
  simp only [x8_dm_mul]
  rw [x8_to_smulf, smul_kronecker, kronecker_smul, smul_smul]

/-- anticommutation count. -/
def x8N {m : ℕ} (a : Option Axis) (f : Fin m → Option Axis) (b : Option Axis)
    (g : Fin m → Option Axis) : ℕ :=
  (if antiO a b then 1 else 0) + (Finset.univ.filter fun i => antiO (f i) (g i)).card

theorem x8_K_comm {m : ℕ} (a b : Option Axis) (f g : Fin m → Option Axis) :
    x8K a f * x8K b g = ((-1 : ℂ) ^ x8N a f b g) • (x8K b g * x8K a f) := by
  unfold x8K
  rw [← mul_kronecker_mul, x8_to_mul, ← mul_kronecker_mul, x8_to_mul]
  rw [x8_dm_comm a b]
  simp only [x8_dm_comm (f _) (g _)]
  rw [x8_to_smulf, smul_kronecker, kronecker_smul, smul_smul]
  congr 1
  unfold x8N
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, pow_add]
  split_ifs <;> simp

theorem x8_K_sq {m : ℕ} (a : Option Axis) (f : Fin m → Option Axis) :
    x8K a f * x8K a f = 1 := by
  unfold x8K
  rw [← mul_kronecker_mul, x8_to_mul]
  simp only [x8_dm_sq]
  rw [x8_to_one, one_kronecker_one]

theorem x8_K_H {m : ℕ} (a : Option Axis) (f : Fin m → Option Axis) :
    (x8K a f)ᴴ = x8K a f := by
  unfold x8K
  rw [conjTranspose_kronecker, x8_to_H]
  simp only [x8_dm_H]

/-- a nonzero multiple of a Pauli word. -/
def IsPW {m : ℕ} (W : Op (Bool × Qubits m)) (a : Option Axis) (f : Fin m → Option Axis) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ W = c • x8K a f

theorem x8_qr_HH {I : Type} [Fintype I] [DecidableEq I] (M : Op I) (hM : Mᴴ = M) :
    (quarterRotation M)ᴴ = quarterRotation (-M) := by
  rw [x8_qr_H M hM]
  unfold quarterRotation
  rw [smul_neg, sub_neg_eq_add]

theorem x8_qrf_comm {I : Type} [Fintype I] [DecidableEq I] (M A : Op I) (hM : Mᴴ = M)
    (hMM : M * M = 1) (h : A * M = M * A) :
    quarterRotation M * A * (quarterRotation M)ᴴ = A := by
  have hM' : (-M)ᴴ = -M := by rw [conjTranspose_neg, hM]
  have e : quarterRotation M = (quarterRotation (-M))ᴴ := by
    rw [x8_qr_HH (-M) hM', neg_neg]
  rw [x8_qr_HH M hM, e]
  exact x8_qr_comm (-M) A hM' (by rw [neg_mul_neg, hMM]) (by rw [Matrix.mul_neg, Matrix.neg_mul, h])

theorem x8_qrf_anti {I : Type} [Fintype I] [DecidableEq I] (M A : Op I) (hM : Mᴴ = M)
    (hMM : M * M = 1) (h : A * M = -(M * A)) :
    quarterRotation M * A * (quarterRotation M)ᴴ = (-Complex.I) • (M * A) := by
  have hM' : (-M)ᴴ = -M := by rw [conjTranspose_neg, hM]
  have e : quarterRotation M = (quarterRotation (-M))ᴴ := by
    rw [x8_qr_HH (-M) hM', neg_neg]
  rw [x8_qr_HH M hM, e]
  rw [x8_qr_anti (-M) A hM' (by rw [neg_mul_neg, hMM])
    (by rw [Matrix.mul_neg, Matrix.neg_mul, h])]
  rw [Matrix.neg_mul, smul_neg, neg_smul]

/-- label update under conjugation by the quarter rotation of the P word. -/
def stepL {m : ℕ} (P : Axis) (a : Option Axis) (f : Fin m → Option Axis) :
    Option Axis × (Fin m → Option Axis) :=
  if Even (x8N a f (some P) (fun _ => some P)) then (a, f)
  else (mulO (some P) a, fun i => mulO (some P) (f i))

theorem x8_step {m : ℕ} (P : Axis) {W : Op (Bool × Qubits m)} {a : Option Axis}
    {f : Fin m → Option Axis} (h : IsPW W a f) :
    IsPW (quarterRotation (x8K (some P) (fun _ => some P)) * W *
      (quarterRotation (x8K (some P) (fun _ => some P)))ᴴ) (stepL P a f).1 (stepL P a f).2 := by
  obtain ⟨c, hc, rfl⟩ := h
  have hc' := x8_K_comm a (some P) f (fun _ => some P)
  unfold stepL
  split_ifs with hN
  · refine ⟨c, hc, ?_⟩
    apply x8_qrf_comm _ _ (x8_K_H _ _) (x8_K_sq _ _)
    rw [Matrix.smul_mul, Matrix.mul_smul, hc', hN.neg_one_pow, one_smul]
  · rw [x8_qrf_anti _ _ (x8_K_H _ _) (x8_K_sq _ _)]
    · rw [Matrix.mul_smul, x8_K_mul, smul_smul, smul_smul]
      refine ⟨_, ?_, rfl⟩
      refine mul_ne_zero (mul_ne_zero (by simp) hc) (mul_ne_zero (x8_phO_ne _ _) ?_)
      exact Finset.prod_ne_zero_iff.mpr fun i _ => x8_phO_ne _ _
    · rw [Matrix.smul_mul, Matrix.mul_smul, hc', (Nat.not_even_iff_odd.mp hN).neg_one_pow,
        neg_one_smul, smul_neg]

end X8P22


open scoped ComplexConjugate ComplexOrder Matrix Kronecker

noncomputable section

namespace X8P22
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22 Matrix

theorem x8_antiO_none (x : Option Axis) : antiO x none = false := by
  rcases x with _ | x <;> rfl

theorem x8_dm_none : directionMatrix none = 1 := rfl
theorem x8_dm_some (b : Axis) : directionMatrix (some b) = axisMatrix b := rfl

theorem x8_K_ne {m : ℕ} (a : Option Axis) (f : Fin m → Option Axis) : x8K a f ≠ 0 := by
  intro h
  have := x8_K_sq a f
  rw [h, Matrix.zero_mul] at this
  exact zero_ne_one this

theorem x8_src {m : ℕ} {W : Op (Bool × Qubits m)} {a : Option Axis} {f : Fin m → Option Axis}
    (h : IsPW W a f) : SourceOnly m W ↔ ∀ i, f i = none := by
  obtain ⟨c, hc, rfl⟩ := h
  constructor
  · rintro ⟨B, hB⟩ j
    by_contra hj
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hj
    let τ : Axis := if b = .X then .Z else .X
    have hbt : antiO (some b) (some τ) = true := by
      simp only [antiO, τ]; split_ifs with h1 <;> simp [h1]
    let g : Fin m → Option Axis := Function.update (fun _ => none) j (some τ)
    have hN : x8N a f none g = 1 := by
      unfold x8N
      rw [x8_antiO_none]
      simp only [Bool.false_eq_true, if_false, zero_add]
      rw [Finset.card_eq_one]
      refine ⟨j, ?_⟩
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hi
        by_contra hij
        simp [g, Function.update_of_ne hij, x8_antiO_none] at hi
      · rintro rfl
        simp [g, hb, hbt]
    have hcomm := x8_K_comm a none f g
    rw [hN, pow_one, neg_one_smul] at hcomm
    -- W commutes with x8K none g
    have hW : (c • x8K a f) * x8K none g = x8K none g * (c • x8K a f) := by
      rw [hB]
      unfold x8K
      simp only [Matrix.kronecker, x8_dm_none]
      rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
        Matrix.mul_one, Matrix.one_mul]
    rw [Matrix.smul_mul, Matrix.mul_smul, hcomm] at hW
    have h2 : (2 * c) • (x8K none g * x8K a f) = 0 := by
      rw [mul_smul, two_smul]
      rw [smul_neg] at hW
      nth_rewrite 1 [← hW]; exact neg_add_cancel _
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact hc (by simpa using h3)
    · have : x8K none g * (x8K none g * x8K a f) = 0 := by rw [h3, Matrix.mul_zero]
      rw [← Matrix.mul_assoc, x8_K_sq, Matrix.one_mul] at this
      exact x8_K_ne a f this
  · intro hf
    refine ⟨c • directionMatrix a, ?_⟩
    have : f = fun _ => none := funext hf
    subst this
    unfold x8K
    simp only [Matrix.kronecker, x8_dm_none]
    rw [x8_to_one, smul_kronecker]

theorem x8_dir {m : ℕ} {W : Op (Bool × Qubits m)} {a : Option Axis} {b : Axis}
    (h : IsPW W a (fun _ => some b)) (i : Fin m) : HasSignalDirection W i b := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun x y => c * directionMatrix a x.1 y.1 *
    ∏ j : {j : Fin m // j ≠ i}, axisMatrix b (x.2 j) (y.2 j), fun p q => ?_⟩
  have e : x8K a (fun _ : Fin m => some b) p q =
      directionMatrix a p.1 q.1 * ∏ j, axisMatrix b (p.2 j) (q.2 j) := rfl
  rw [Matrix.smul_apply, e, smul_eq_mul, Fintype.prod_eq_mul_prod_subtype_ne _ i]
  ring

theorem x8_enc (m : ℕ) (P Q : Axis) :
    sectorEncoder m P Q = quarterRotation (x8K (some P) (fun _ : Fin m => some P)) *
      quarterRotation (x8K (some Q) (fun _ : Fin m => some Q)) := rfl

theorem x8_conj {m : ℕ} (P Q : Axis) {S : Op (Bool × Qubits m)} {a : Option Axis}
    {f : Fin m → Option Axis} (h : IsPW S a f) :
    IsPW (sectorEncoder m P Q * S * (sectorEncoder m P Q)ᴴ)
      (stepL P (stepL Q a f).1 (stepL Q a f).2).1 (stepL P (stepL Q a f).1 (stepL Q a f).2).2 := by
  have h1 := x8_step Q h
  have h2 := x8_step P h1
  rw [x8_enc, conjTranspose_mul]
  convert h2 using 1
  simp only [Matrix.mul_assoc]

theorem x8_N_const {m : ℕ} (a c : Option Axis) (P : Axis) :
    x8N a (fun _ : Fin m => c) (some P) (fun _ => some P) =
      (if antiO a (some P) then 1 else 0) + (if antiO c (some P) then m else 0) := by
  unfold x8N
  congr 1
  split_ifs with h <;> simp [h]

theorem x8_mulO_eq (q x p : Option Axis) : mulO q x = p ↔ x = mulO q p := by
  rcases q with _ | q <;> rcases x with _ | x <;> rcases p with _ | p
  all_goals try (cases q)
  all_goals try (cases x)
  all_goals try (cases p)
  all_goals simp [mulO, remainingAxis]

theorem x8_const_of {m : ℕ} (P Q : Axis) (l : Fin m → Option Axis)
    (h : ∀ i, (stepL P (stepL Q none l).1 (stepL Q none l).2).2 i = none) :
    ∃ c, l = fun _ => c := by
  unfold stepL at h
  split_ifs at h
  · exact ⟨none, funext h⟩
  · exact ⟨mulO (some P) none, funext fun i => (x8_mulO_eq _ _ _).mp (h i)⟩
  · exact ⟨mulO (some Q) none, funext fun i => (x8_mulO_eq _ _ _).mp (h i)⟩
  · exact ⟨mulO (some Q) (mulO (some P) none),
      funext fun i => (x8_mulO_eq _ _ _).mp ((x8_mulO_eq _ _ _).mp (h i))⟩

end X8P22


open scoped ComplexConjugate ComplexOrder Matrix Kronecker

noncomputable section

namespace X8P22
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22 Matrix

theorem x8_final (m : ℕ) (hm : 0 < m) (P Q : Axis) (hPQ : P ≠ Q) (c : Option Axis) :
    (∀ i : Fin m, (stepL P (stepL Q none (fun _ : Fin m => c)).1 (stepL Q none (fun _ : Fin m => c)).2).2 i = none) ↔
      (c = none ∨ (Odd m ∧ c = some (remainingAxis P Q))) := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rcases Nat.even_or_odd m with h2 | h2
  · have h3 : ¬ Odd m := Nat.not_odd_iff_even.mpr h2
    rcases c with _ | c <;> cases P <;> cases Q <;> (try cases c) <;>
      first | exact absurd rfl hPQ | simp [h2, h3, stepL, x8_N_const, antiO, mulO, remainingAxis, Nat.even_add]
  · have h3 : ¬ Even m := Nat.not_even_iff_odd.mpr h2
    rcases c with _ | c <;> cases P <;> cases Q <;> (try cases c) <;>
      first | exact absurd rfl hPQ | simp [h2, h3, stepL, x8_N_const, antiO, mulO, remainingAxis, Nat.even_add]

def fperm (m : ℕ) (P Q : Axis) : Equiv.Perm Axis :=
  if Even m then (Equiv.swap P Q).trans (Equiv.swap Q (remainingAxis P Q)) else Equiv.swap P Q

theorem x8_final3 (m : ℕ) (P Q : Axis) (hPQ : P ≠ Q) (a : Axis) :
    (stepL P (stepL Q (some a) (fun _ : Fin m => none)).1
      (stepL Q (some a) (fun _ : Fin m => none)).2).2 = fun _ => some (fperm m P Q a) := by
  rcases Nat.even_or_odd m with h2 | h2
  · have h3 : ¬ Odd m := Nat.not_odd_iff_even.mpr h2
    cases a <;> cases P <;> cases Q <;> first | exact absurd rfl hPQ |
      simp [h2, h3, stepL, x8_N_const, antiO, mulO, remainingAxis, Nat.even_add, fperm,
        Equiv.swap_apply_def]
  · have h3 : ¬ Even m := Nat.not_even_iff_odd.mpr h2
    cases a <;> cases P <;> cases Q <;> first | exact absurd rfl hPQ |
      simp [h2, h3, stepL, x8_N_const, antiO, mulO, remainingAxis, Nat.even_add, fperm,
        Equiv.swap_apply_def]

end X8P22


open scoped ComplexConjugate ComplexOrder Matrix Kronecker

noncomputable section

namespace X8P22
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22 Matrix

/-- global Pauli word over k sectors. -/
def x8GW {m k : ℕ} (a : Fin k → Option Axis) (F : Fin k → Fin m → Option Axis) :
    Op (Qubits k × Signals m k) :=
  x8st (fun j => x8K (a j) (F j))

theorem x8_st_smul {m k : ℕ} (c : Fin k → ℂ) (M : Fin k → Op (Bool × Qubits m)) :
    x8st (fun j => c j • M j) = (∏ j, c j) • x8st M := by
  ext a b
  simp [x8st, Finset.prod_mul_distrib]

theorem x8_st_kron' {m k : ℕ} (y : Fin k → Op Bool) (z : Fin k → Op (Qubits m)) :
    x8st (fun j => Matrix.kronecker (y j) (z j)) = Matrix.kronecker (tensorOps y) (x8sz z) :=
  x8_st_kron y z

theorem x8_st_one {m k : ℕ} : x8st (fun _ : Fin k => (1 : Op (Bool × Qubits m))) = 1 := by
  have e : (fun _ : Fin k => (1 : Op (Bool × Qubits m))) =
      fun j => (fun _ : Fin k => (1 : Op Bool)) j ⊗ₖ (fun _ : Fin k => (1 : Op (Qubits m))) j :=
    funext fun _ => one_kronecker_one.symm
  rw [e, x8_st_kron, x8_to_one, x8_sz_one, one_kronecker_one]

theorem x8_GW_sq {m k : ℕ} (a : Fin k → Option Axis) (F : Fin k → Fin m → Option Axis) :
    x8GW a F * x8GW a F = 1 := by
  unfold x8GW
  rw [x8_st_mul]
  simp only [x8_K_sq]
  exact x8_st_one

theorem x8_GW_comm {m k : ℕ} (a b : Fin k → Option Axis) (F G : Fin k → Fin m → Option Axis) :
    x8GW a F * x8GW b G = (∏ j, (-1 : ℂ) ^ x8N (a j) (F j) (b j) (G j)) • (x8GW b G * x8GW a F) := by
  unfold x8GW
  rw [x8_st_mul, x8_st_mul]
  simp only [x8_K_comm (a _) (b _) (F _) (G _)]
  rw [x8_st_smul]

theorem x8_GW_ne {m k : ℕ} (a : Fin k → Option Axis) (F : Fin k → Fin m → Option Axis) :
    x8GW a F ≠ 0 := by
  intro h
  have := x8_GW_sq a F
  rw [h, Matrix.zero_mul] at this
  exact zero_ne_one this

theorem x8_sz_to {m k : ℕ} (g : Wires m k → Op Bool) :
    x8sz (fun j => tensorOps (fun i => g (j, i))) = tensorOps g := by
  ext s s'
  simp only [x8sz, tensorOps]
  rw [← Finset.univ_product_univ, Finset.prod_product]

theorem x8_GW_none {m k : ℕ} (a : Fin k → Option Axis) :
    x8GW a (fun _ _ => none : Fin k → Fin m → Option Axis) =
      Matrix.kronecker (tensorOps fun j => directionMatrix (a j)) (1 : Op (Signals m k)) := by
  unfold x8GW x8K
  simp only [x8_dm_none]
  rw [x8_to_one, x8_st_kron, x8_sz_one]
  rfl

theorem x8_GW_sig {m k : ℕ} (F : Fin k → Fin m → Option Axis) :
    x8GW (fun _ => none) F = Matrix.kronecker (1 : Op (Qubits k))
      (tensorOps fun w : Wires m k => directionMatrix (F w.1 w.2)) := by
  unfold x8GW x8K
  simp only [x8_dm_none]
  rw [x8_st_kron, x8_to_one]
  rw [x8_sz_to (fun w : Wires m k => directionMatrix (F w.1 w.2))]
  rfl

theorem x8_gsrc {m k : ℕ} {c : ℂ} (hc : c ≠ 0) (a : Fin k → Option Axis)
    (F : Fin k → Fin m → Option Axis) :
    (∃ M : Op (Qubits k), c • x8GW a F = Matrix.kronecker M (1 : Op (Signals m k))) ↔
      ∀ j i, F j i = none := by
  constructor
  · rintro ⟨B, hB⟩ j0 i0
    by_contra hj
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hj
    let τ : Axis := if b = .X then .Z else .X
    have hbt : antiO (some b) (some τ) = true := by
      simp only [antiO, τ]; split_ifs with h1 <;> simp [h1]
    let G : Fin k → Fin m → Option Axis := fun j =>
      if j = j0 then Function.update (fun _ => none) i0 (some τ) else fun _ => none
    have hN : ∀ j, x8N (a j) (F j) none (G j) = if j = j0 then 1 else 0 := by
      intro j
      unfold x8N
      rw [x8_antiO_none]
      simp only [Bool.false_eq_true, if_false, zero_add]
      by_cases hj : j = j0
      · subst hj
        rw [if_pos rfl, Finset.card_eq_one]
        refine ⟨i0, ?_⟩
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hi
          by_contra hij
          simp [G, Function.update_of_ne hij, x8_antiO_none] at hi
        · rintro rfl
          simp [G, hb, hbt]
      · rw [if_neg hj, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _
        simp [G, hj, x8_antiO_none]
    have hcomm := x8_GW_comm a (fun _ => none) F G
    have hp : (∏ j, (-1 : ℂ) ^ x8N (a j) (F j) none (G j)) = -1 := by
      simp only [hN]
      rw [Finset.prod_eq_single j0]
      · simp
      · intro j _ hj; simp [hj]
      · simp
    rw [hp, neg_one_smul] at hcomm
    have hW : (c • x8GW a F) * x8GW (fun _ => none) G = x8GW (fun _ => none) G * (c • x8GW a F) := by
      rw [hB, x8_GW_sig]
      simp only [Matrix.kronecker]
      rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
        Matrix.mul_one, Matrix.one_mul]
    rw [Matrix.smul_mul, Matrix.mul_smul, hcomm] at hW
    have h2 : (2 * c) • (x8GW (fun _ => none) G * x8GW a F) = 0 := by
      rw [mul_smul, two_smul]
      rw [smul_neg] at hW
      nth_rewrite 1 [← hW]; exact neg_add_cancel _
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact hc (by simpa using h3)
    · have : x8GW (fun _ => none) G * (x8GW (fun _ => none) G * x8GW a F) = 0 := by
        rw [h3, Matrix.mul_zero]
      rw [← Matrix.mul_assoc, x8_GW_sq, Matrix.one_mul] at this
      exact x8_GW_ne a F this
  · intro hF
    have : F = fun _ _ => none := funext fun j => funext fun i => hF j i
    subst this
    refine ⟨c • tensorOps fun j => directionMatrix (a j), ?_⟩
    rw [x8_GW_none]
    simp only [Matrix.kronecker]
    rw [smul_kronecker]

theorem x8_gconj {m k : ℕ} (P Q : Axis) (a : Fin k → Option Axis) (F : Fin k → Fin m → Option Axis) :
    ∃ d : ℂ, d ≠ 0 ∧ twoPauliEncoder m k P Q * x8GW a F * (twoPauliEncoder m k P Q)ᴴ =
      d • x8GW (fun j => (stepL P (stepL Q (a j) (F j)).1 (stepL Q (a j) (F j)).2).1)
        (fun j => (stepL P (stepL Q (a j) (F j)).1 (stepL Q (a j) (F j)).2).2) := by
  have h : ∀ j, IsPW (sectorEncoder m P Q * x8K (a j) (F j) * (sectorEncoder m P Q)ᴴ)
      (stepL P (stepL Q (a j) (F j)).1 (stepL Q (a j) (F j)).2).1
      (stepL P (stepL Q (a j) (F j)).1 (stepL Q (a j) (F j)).2).2 :=
    fun j => x8_conj P Q ⟨1, one_ne_zero, (one_smul ℂ _).symm⟩
  choose d hd hW using h
  refine ⟨∏ j, d j, Finset.prod_ne_zero_iff.mpr fun j _ => hd j, ?_⟩
  have e : twoPauliEncoder m k P Q = x8st (fun _ => sectorEncoder m P Q) := rfl
  rw [e, x8_st_H]
  unfold x8GW
  rw [x8_st_mul, x8_st_mul]
  simp only [hW]
  rw [x8_st_smul]

end X8P22


open scoped ComplexConjugate ComplexOrder Matrix Kronecker

noncomputable section

namespace X8P22
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22 Matrix

/-- Pauli label of a binary (x,z) pair. -/
def toL (p : ZMod 2 × ZMod 2) : Option Axis :=
  if p.1 = 0 then (if p.2 = 0 then none else some .Z) else (if p.2 = 0 then some .X else some .Y)

theorem x8_Z2 (t : ZMod 2) : t = 0 ∨ t = 1 := by
  fin_cases t
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem x8_toL_mul (p q : ZMod 2 × ZMod 2) : mulO (toL p) (toL q) = toL (p + q) := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  rcases x8_Z2 p1 with rfl | rfl <;> rcases x8_Z2 p2 with rfl | rfl <;>
    rcases x8_Z2 q1 with rfl | rfl <;> rcases x8_Z2 q2 with rfl | rfl <;>
    simp [toL, mulO, remainingAxis] <;> decide

/-- signal Pauli word with binary labels. -/
def x8SW {m k : ℕ} (u : Wires m k → ZMod 2 × ZMod 2) : Op (Signals m k) :=
  tensorOps (fun w => directionMatrix (toL (u w)))

theorem x8_SW_mul {m k : ℕ} (u v : Wires m k → ZMod 2 × ZMod 2) :
    x8SW u * x8SW v = (∏ w, phO (toL (u w)) (toL (v w))) • x8SW (u + v) := by
  unfold x8SW
  rw [x8_to_mul]
  simp only [x8_dm_mul, x8_toL_mul]
  rw [x8_to_smulf]
  rfl

theorem x8_SW_zero {m k : ℕ} : x8SW (0 : Wires m k → ZMod 2 × ZMod 2) = 1 := by
  unfold x8SW
  have : ∀ w : Wires m k, directionMatrix (toL ((0 : Wires m k → ZMod 2 × ZMod 2) w)) = 1 := by
    intro w; simp [toL, x8_dm_none]
  simp only [this]
  exact x8_to_one

def IsSW {m k : ℕ} (T : Op (Signals m k)) (u : Wires m k → ZMod 2 × ZMod 2) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ T = c • x8SW u

theorem x8_SW_prod {m k : ℕ} (n : ℕ) (Fs : Fin n → Op (Signals m k))
    (us : Fin n → Wires m k → ZMod 2 × ZMod 2) (h : ∀ i, IsSW (Fs i) (us i)) :
    IsSW (List.ofFn Fs).prod (∑ i, us i) := by
  induction n with
  | zero => exact ⟨1, one_ne_zero, by simp [x8_SW_zero]⟩
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    obtain ⟨c, hc, e⟩ := h 0
    obtain ⟨d, hd, e'⟩ := ih (fun i => Fs i.succ) (fun i => us i.succ) (fun i => h i.succ)
    rw [e, e', Matrix.smul_mul, Matrix.mul_smul, x8_SW_mul, smul_smul, smul_smul]
    exact ⟨_, mul_ne_zero (mul_ne_zero hc hd)
      (Finset.prod_ne_zero_iff.mpr fun _ _ => x8_phO_ne _ _), rfl⟩

def genL {m k : ℕ} (A : Matrix (Wires m k) (Wires m k) F2) (v : Wires m k) :
    Wires m k → ZMod 2 × ZMod 2 :=
  fun w => (if w = v then 1 else 0, A v w)

theorem x8_gen {m k : ℕ} (A : Matrix (Wires m k) (Wires m k) F2) (hdiag : ∀ a, A a a = 0)
    (v : Wires m k) : signalGenerator A v = x8SW (genL A v) := by
  unfold signalGenerator x8SW
  congr 1
  funext w
  by_cases hw : w = v
  · subst hw
    rw [if_pos rfl]
    simp [genL, toL, hdiag, x8_dm_some, axisMatrix]
  · rw [if_neg hw]
    rcases x8_Z2 (A v w) with h0 | h1
    · rw [if_neg (by rw [h0]; decide)]
      simp [genL, toL, hw, h0, x8_dm_none]
    · rw [if_pos h1]
      simp [genL, toL, hw, h1, x8_dm_some, axisMatrix]

theorem x8_stab {m k : ℕ} (A : Matrix (Wires m k) (Wires m k) F2) (hsym : ∀ a b, A a b = A b a)
    (hdiag : ∀ a, A a a = 0) (x : Wires m k → F2) :
    IsSW (signalStabilizer A x) (fun w => (x w, A.mulVec x w)) := by
  let e := Fintype.equivFin (Wires m k)
  have hsum : (fun w => (x w, A.mulVec x w)) =
      ∑ a : Fin (Fintype.card (Wires m k)), x (e.symm a) • genL A (e.symm a) := by
    rw [Equiv.sum_comp e.symm (fun v => x v • genL A v)]
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, genL, Prod.smul_mk, smul_eq_mul]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
      simp
    · rw [Prod.snd_sum]
      simp only [mulVec, dotProduct]
      exact Finset.sum_congr rfl fun v _ => by rw [hsym, mul_comm]
  unfold signalStabilizer
  rw [hsum]
  apply x8_SW_prod
  intro i
  dsimp only
  split_ifs with h
  · exact ⟨1, one_ne_zero, by rw [x8_gen A hdiag, h, one_smul, one_smul]⟩
  · have h0 : x (e.symm i) = 0 := (x8_Z2 _).resolve_right h
    exact ⟨1, one_ne_zero, by rw [h0, zero_smul, x8_SW_zero, one_smul]⟩

theorem x8_stabGW {m k : ℕ} (A : Matrix (Wires m k) (Wires m k) F2) (hsym : ∀ a b, A a b = A b a)
    (hdiag : ∀ a, A a a = 0) (x : Wires m k → F2) :
    ∃ c : ℂ, c ≠ 0 ∧ Matrix.kronecker (1 : Op (Qubits k)) (signalStabilizer A x) =
      c • x8GW (fun _ => none) (fun j i => toL (x (j, i), A.mulVec x (j, i))) := by
  obtain ⟨c, hc, e⟩ := x8_stab A hsym hdiag x
  refine ⟨c, hc, ?_⟩
  rw [x8_GW_sig, e]
  simp only [Matrix.kronecker]
  rw [kronecker_smul]
  rfl

end X8P22


open scoped ComplexConjugate ComplexOrder Matrix Kronecker

noncomputable section

namespace X8P22
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22 Matrix

theorem x8_sector_iff (m : ℕ) (hm : 0 < m) (P Q : Axis) (hPQ : P ≠ Q) (l : Fin m → Option Axis) :
    (∀ i, (stepL P (stepL Q none l).1 (stepL Q none l).2).2 i = none) ↔
      (∀ i, l i = none) ∨ (Odd m ∧ ∀ i, l i = some (remainingAxis P Q)) := by
  constructor
  · intro h
    obtain ⟨c, rfl⟩ := x8_const_of P Q l h
    rcases (x8_final m hm P Q hPQ c).mp h with rfl | ⟨ho, rfl⟩
    · exact Or.inl fun _ => rfl
    · exact Or.inr ⟨ho, fun _ => rfl⟩
  · rintro (h | ⟨ho, h⟩)
    · have : l = fun _ => none := funext h
      subst this
      exact (x8_final m hm P Q hPQ none).mpr (Or.inl rfl)
    · have : l = fun _ => some (remainingAxis P Q) := funext h
      subst this
      exact (x8_final m hm P Q hPQ _).mpr (Or.inr ⟨ho, rfl⟩)

theorem x8_ev_iff (m k : ℕ) (hm : 1 ≤ m) (P Q : Axis) (hPQ : P ≠ Q) (G : CutGraph (Wires m k))
    (x : Wires m k → F2) :
    ExceptionalVector P Q G x ↔ ∀ j : Fin k,
      (∀ i, toL (x (j, i), G.AS.mulVec x (j, i)) = none) ∨
      (Odd m ∧ ∀ i, toL (x (j, i), G.AS.mulVec x (j, i)) = some (remainingAxis P Q)) := by
  obtain ⟨c, hc, e⟩ := x8_stabGW G.AS G.symS G.diagS x
  obtain ⟨d, hd, e2⟩ := x8_gconj P Q (fun _ => none)
    (fun j i => toL (x (j, i), G.AS.mulVec x (j, i)))
  unfold ExceptionalVector
  rw [e, Matrix.mul_smul, Matrix.smul_mul, e2, smul_smul]
  rw [x8_gsrc (mul_ne_zero hc hd)]
  exact forall_congr' fun j => x8_sector_iff m hm P Q hPQ _

theorem x8_toL_none (p : ZMod 2 × ZMod 2) : toL p = none ↔ p.1 = 0 ∧ p.2 = 0 := by
  obtain ⟨a, b⟩ := p
  rcases x8_Z2 a with rfl | rfl <;> rcases x8_Z2 b with rfl | rfl <;> simp [toL]

theorem x8_toL_some (p : ZMod 2 × ZMod 2) (r : Axis) : toL p = some r ↔
    (r = .X ∧ p.1 = 1 ∧ p.2 = 0) ∨ (r = .Y ∧ p.1 = 1 ∧ p.2 = 1) ∨ (r = .Z ∧ p.1 = 0 ∧ p.2 = 1) := by
  obtain ⟨a, b⟩ := p
  rcases x8_Z2 a with rfl | rfl <;> rcases x8_Z2 b with rfl | rfl <;> cases r <;> simp [toL]

theorem x8_quad {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι (ZMod 2))
    (hsym : ∀ a b, A a b = A b a) (hdiag : ∀ a, A a a = 0) (x : ι → ZMod 2) :
    x ⬝ᵥ (A.mulVec x) = 0 := by
  let e := Fintype.equivFin ι
  let f : ι → ι → ZMod 2 := fun v w => x v * (A v w * x w)
  let g : ι → ι → ZMod 2 := fun v w => if e v < e w then f v w else 0
  have hfg : ∀ v w, f v w = g v w + g w v := by
    intro v w
    rcases lt_trichotomy (e v) (e w) with h | h | h
    · simp [g, h, not_lt.mpr h.le]
    · have : v = w := e.injective h
      subst this
      simp [f, g, hdiag]
    · simp only [g, if_neg (not_lt.mpr h.le), if_pos h, zero_add]
      simp only [f]
      rw [hsym]; ring
  have h1 : x ⬝ᵥ (A.mulVec x) = ∑ v, ∑ w, f v w := by
    simp only [dotProduct, mulVec, Finset.mul_sum, f]
  rw [h1]
  simp_rw [hfg, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun v w => g w v), ← two_mul]
  exact zero_mul _

theorem x8_rem_XZ (P Q : Axis) (h : classXZ P Q) : remainingAxis P Q = .Y := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [remainingAxis]

theorem x8_rem_YZ (P Q : Axis) (h : classYZ P Q) : remainingAxis P Q = .X := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [remainingAxis]

theorem x8_rem_XY (P Q : Axis) (hPQ : P ≠ Q) (h1 : ¬ classXZ P Q) (h2 : ¬ classYZ P Q) :
    remainingAxis P Q = .Z := by
  cases P <;> cases Q <;> simp_all [classXZ, classYZ, remainingAxis]

theorem x8_two (t : ZMod 2) : t + t = 0 := by
  rcases x8_Z2 t with rfl | rfl <;> decide

theorem x8_sq2 (t : ZMod 2) : t * t = t := by
  rcases x8_Z2 t with rfl | rfl <;> decide

theorem x8_eq_of_add (s t : ZMod 2) (h : s + t = 0) : s = t := by
  rcases x8_Z2 s with rfl | rfl <;> rcases x8_Z2 t with rfl | rfl <;> first | rfl | exact absurd h (by decide)

theorem x8_F2 (m k : ℕ) (hm : 2 ≤ m) (P Q : Axis) (hPQ : P ≠ Q)
    (A : Matrix (Wires m k) (Wires m k) F2) (hsym : ∀ a b, A a b = A b a) (hdiag : ∀ a, A a a = 0)
    (x : Wires m k → F2) :
    (∀ j : Fin k, (∀ i, toL (x (j, i), A.mulVec x (j, i)) = none) ∨
      (Odd m ∧ ∀ i, toL (x (j, i), A.mulVec x (j, i)) = some (remainingAxis P Q))) ↔
      x ∈ exceptionalSpace P Q A := by
  have i0 : Fin m := ⟨0, by omega⟩
  unfold exceptionalSpace
  split_ifs with he hxz hyz
  · -- even m
    rw [Set.mem_singleton_iff]
    constructor
    · intro h
      funext w
      rcases h w.1 with h1 | ⟨ho, _⟩
      · exact ((x8_toL_none _).mp (h1 w.2)).1
      · exact absurd ho (Nat.not_odd_iff_even.mpr he)
    · rintro rfl j
      left; intro i
      simp [toL]
  · -- odd, XZ: Y-type
    have ho : Odd m := Nat.not_even_iff_odd.mp he
    rw [x8_rem_XZ P Q hxz]
    constructor
    · intro h
      have hval : ∀ j i, A.mulVec x (j, i) = x (j, i) ∧ x (j, i) = x (j, i0) := by
        intro j i
        rcases h j with h1 | ⟨_, h1⟩
        · have a1 := (x8_toL_none _).mp (h1 i)
          have a2 := (x8_toL_none _).mp (h1 i0)
          exact ⟨a1.2.trans a1.1.symm, a1.1.trans a2.1.symm⟩
        · have a1 := (x8_toL_some _ _).mp (h1 i)
          have a2 := (x8_toL_some _ _).mp (h1 i0)
          simp only [reduceCtorEq, false_and, false_or, or_false, true_and] at a1 a2
          exact ⟨a1.2.trans a1.1.symm, a1.1.trans a2.1.symm⟩
      have hx : x = sectorIndicator (fun j => x (j, i0)) := funext fun w => (hval w.1 w.2).2
      have hAx : A.mulVec x = x := funext fun w => (hval w.1 w.2).1
      refine ⟨fun j => x (j, i0), hx, ?_, ?_⟩
      · rw [Matrix.add_mulVec, hAx, one_mulVec]
        funext w
        exact x8_two _
      · have hq := x8_quad A hsym hdiag x
        rw [hAx] at hq
        have hxx : x ⬝ᵥ x = (m : ZMod 2) * ∑ j, x (j, i0) := by
          simp only [dotProduct, x8_sq2]
          rw [← Finset.univ_product_univ, Finset.sum_product, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_congr rfl fun i _ => (hval j i).2]
          simp
        rw [hxx] at hq
        have hm1 : (m : ZMod 2) = 1 := by
          rw [← ZMod.natCast_mod, Nat.odd_iff.mp ho]; rfl
        rw [hm1, one_mul] at hq
        exact hq
    · rintro ⟨c, rfl, h2, _⟩
      have hAx : A.mulVec (sectorIndicator c) = sectorIndicator c := by
        funext w
        have := congrFun h2 w
        rw [Matrix.add_mulVec, one_mulVec] at this
        exact x8_eq_of_add _ _ this
      intro j
      rcases x8_Z2 (c j) with h0 | h1
      · left; intro i
        rw [hAx]; simp [sectorIndicator, h0, toL]
      · right; refine ⟨ho, fun i => ?_⟩
        rw [hAx]; simp [sectorIndicator, h1, toL]
  · -- odd, YZ: X-type
    have ho : Odd m := Nat.not_even_iff_odd.mp he
    rw [x8_rem_YZ P Q hyz]
    constructor
    · intro h
      have hval : ∀ j i, A.mulVec x (j, i) = 0 ∧ x (j, i) = x (j, i0) := by
        intro j i
        rcases h j with h1 | ⟨_, h1⟩
        · have a1 := (x8_toL_none _).mp (h1 i)
          have a2 := (x8_toL_none _).mp (h1 i0)
          exact ⟨a1.2, a1.1.trans a2.1.symm⟩
        · have a1 := (x8_toL_some _ _).mp (h1 i)
          have a2 := (x8_toL_some _ _).mp (h1 i0)
          simp only [reduceCtorEq, false_and, or_false, true_and] at a1 a2
          exact ⟨a1.2, a1.1.trans a2.1.symm⟩
      exact ⟨fun j => x (j, i0), funext fun w => (hval w.1 w.2).2,
        funext fun w => (hval w.1 w.2).1⟩
    · rintro ⟨c, rfl, h2⟩
      intro j
      rcases x8_Z2 (c j) with h0 | h1
      · left; intro i
        rw [h2]; simp [sectorIndicator, h0, toL]
      · right; refine ⟨ho, fun i => ?_⟩
        rw [h2]; simp [sectorIndicator, h1, toL]
  · -- odd, XY: Z-type
    rw [x8_rem_XY P Q hPQ hxz hyz, Set.mem_singleton_iff]
    constructor
    · intro h
      funext w
      rcases h w.1 with h1 | ⟨_, h1⟩
      · exact ((x8_toL_none _).mp (h1 w.2)).1
      · have a1 := (x8_toL_some _ _).mp (h1 w.2)
        simp only [reduceCtorEq, false_and, false_or, true_and] at a1
        exact a1.1
    · rintro rfl j
      left; intro i
      simp [toL]

end X8P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

theorem x8_target (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (P Q : Axis) (hPQ : P ≠ Q) (G : CutGraph (Wires m k))
    (x : Wires m k → F2) (hx : x ∈ cutKernel G) :
    ExceptionalVector P Q G x ↔ x ∈ exceptionalSpace P Q G.AS :=
  (X8P22.x8_ev_iff m k (by omega) P Q hPQ G x).trans
    (X8P22.x8_F2 m k hm P Q hPQ G.AS G.symS G.diagS x)

end

end QAlgorithms.Papers.Independent.Information100.P22

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22 in
/-- Lemma S4, PDF pp.30–31: support definition matches the ambient binary conditions on K. -/
theorem solution (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (P Q : Axis) (hPQ : P ≠ Q) (G : CutGraph (Wires m k))
    (x : Wires m k → F2) (hx : x ∈ cutKernel G) :
    ExceptionalVector P Q G x ↔ x ∈ exceptionalSpace P Q G.AS :=
  x8_target m k hm hk P Q hPQ G x hx
