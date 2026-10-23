-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P22.graphCutSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T21:18:38.243743+00:00
-- url     : https://prove2.me/submissions/a3a736b8-0c13-412f-aac7-09c819fead97

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

theorem x8_Z2' (t : ZMod 2) : t = 0 ∨ t = 1 := by
  fin_cases t
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- sign of a binary phase. -/
def sgn (t : ZMod 2) : ℂ := if t = 0 then 1 else -1

theorem sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  rcases x8_Z2' a with rfl | rfl <;> rcases x8_Z2' b with rfl | rfl <;> simp [sgn] <;> decide

theorem sgn_zero : sgn 0 = 1 := by simp [sgn]

theorem sgn_sq (a : ZMod 2) : sgn a * sgn a = 1 := by
  rw [← sgn_add]
  have : a + a = 0 := by rcases x8_Z2' a with rfl | rfl <;> decide
  rw [this, sgn_zero]

theorem sgn_sum {ι : Type} (s : Finset ι) (f : ι → ZMod 2) :
    sgn (∑ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sgn_add, ih]

theorem bit_inj : Function.Injective bit := by
  intro a b h
  cases a <;> cases b <;> simp_all [bit]

theorem bit_not (b : Bool) : bit (!b) = bit b + 1 := by
  cases b <;> simp [bit] <;> decide

def bv {I : Type} (s : I → Bool) : I → ZMod 2 := fun w => bit (s w)

def ofbv {I : Type} (u : I → ZMod 2) : I → Bool := fun w => decide (u w = 1)

theorem bv_ofbv {I : Type} (u : I → ZMod 2) : bv (ofbv u) = u := by
  funext w
  simp only [bv, ofbv]
  rcases x8_Z2' (u w) with h | h <;> simp [h, bit]

theorem bv_inj {I : Type} : Function.Injective (bv (I := I)) := by
  intro s t h
  funext w
  exact bit_inj (congrFun h w)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- bit-flip permutation matrix. -/
def x8X (y : I → ZMod 2) : Op (I → Bool) :=
  Matrix.of fun s s' => if bv s = bv s' + y then 1 else 0

theorem x8_X_mul (y z : I → ZMod 2) : x8X y * x8X z = x8X (y + z) := by
  ext s s'
  simp only [x8X, mul_apply, of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (ofbv (bv s' + z))]
  · rw [bv_ofbv, if_pos rfl]
    congr 1
    apply propext
    rw [add_assoc, add_comm z y]
  · intro t _ ht
    rw [if_neg]
    intro h
    exact ht (bv_inj (by rw [h, bv_ofbv]))
  · simp

theorem x8_X_zero : x8X (0 : I → ZMod 2) = 1 := by
  ext s s'
  simp only [x8X, of_apply, add_zero, one_apply]
  by_cases h : s = s'
  · subst h; simp
  · rw [if_neg (fun h' => h (bv_inj h')), if_neg h]

theorem x8_X_H (y : I → ZMod 2) : (x8X y)ᴴ = x8X y := by
  ext s s'
  simp only [x8X, conjTranspose_apply, of_apply]
  have : (bv s' = bv s + y) ↔ (bv s = bv s' + y) := by
    constructor <;> intro h <;> rw [h, add_assoc] <;>
      (have : y + y = 0 := funext fun w => by
        rcases x8_Z2' (y w) with h | h <;> simp [h] <;> decide) <;> simp [this]
  by_cases h : bv s = bv s' + y
  · rw [if_pos (this.mpr h), if_pos h]; simp
  · rw [if_neg (fun h' => h (this.mp h')), if_neg h]; simp

theorem x8_X_trace (y : I → ZMod 2) : (x8X y).trace = if y = 0 then (2 : ℂ) ^ Fintype.card I else 0 := by
  simp only [trace, diag, x8X, of_apply]
  by_cases hy : y = 0
  · subst hy
    simp [Fintype.card_fun, Fintype.card_bool]
  · rw [if_neg hy]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [if_neg]
    intro h
    apply hy
    funext w
    have := congrFun h w
    simp only [Pi.add_apply] at this
    simpa using this

/-- graph-state sign diagonal. -/
def x8D (A : Matrix I I F2) : Op (I → Bool) :=
  Matrix.diagonal (fun s => sgn (quadratic A s))

theorem x8_D_sq (A : Matrix I I F2) : x8D A * x8D A = 1 := by
  rw [x8D, diagonal_mul_diagonal]
  simp only [sgn_sq]
  exact diagonal_one

theorem x8_D_H (A : Matrix I I F2) : (x8D A)ᴴ = x8D A := by
  rw [x8D, diagonal_conjTranspose]
  congr 1
  funext s
  simp only [Pi.star_apply, sgn]
  split_ifs <;> simp

end X8P22


open scoped ComplexConjugate ComplexOrder Matrix Kronecker

noncomputable section

namespace X8P22
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22 Matrix

variable {I : Type} [Fintype I] [DecidableEq I]

def ev (v : I) : I → ZMod 2 := fun w => if w = v then 1 else 0

theorem ev_apply (v w : I) : ev v w = if w = v then 1 else 0 := rfl

theorem x8_flip (A : Matrix I I F2) (hsym : ∀ a b, A a b = A b a) (hdiag : ∀ a, A a a = 0)
    (s s' : I → Bool) (v : I) (h : bv s' = bv s + ev v) :
    quadratic A s' = quadratic A s + ∑ w, A v w * bit (s w) := by
  have hb : ∀ a, bit (s' a) = bit (s a) + ev v a := fun a => congrFun h a
  let o := Fintype.equivFin I
  unfold quadratic
  simp only [hb]
  have key : ∀ a b, (if (o a).val < (o b).val then
      A a b * (bit (s a) + ev v a) * (bit (s b) + ev v b) else 0) =
      (if (o a).val < (o b).val then A a b * bit (s a) * bit (s b) else 0) +
      ((if (o a).val < (o b).val then A a b * ev v a * bit (s b) else 0) +
       (if (o a).val < (o b).val then A a b * bit (s a) * ev v b else 0) +
       (if (o a).val < (o b).val then A a b * ev v a * ev v b
         else 0)) := by
    intro a b; split_ifs <;> ring
  simp only [o] at key
  simp only [key, Finset.sum_add_distrib]
  congr 1
  have e1 : ∑ a, ∑ b, (if (o a).val < (o b).val then A a b * ev v a * bit (s b)
      else 0) = ∑ b, if (o v).val < (o b).val then A v b * bit (s b) else 0 := by
    rw [Finset.sum_eq_single v]
    · simp [ev_apply]
    · intro a _ ha
      simp [ev_apply, ha]
    · simp
  have e2 : ∑ a, ∑ b, (if (o a).val < (o b).val then A a b * bit (s a) * ev v b
      else 0) = ∑ a, if (o a).val < (o v).val then A v a * bit (s a) else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single v]
    · simp [hsym a v, ev_apply]
    · intro b _ hb
      simp [ev_apply, hb]
    · simp
  have e3 : ∑ a, ∑ b, (if (o a).val < (o b).val then A a b * ev v a *
      ev v b else 0) = 0 := by
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    split_ifs with hab
    · by_cases ha : a = v
      · subst ha
        have hb : b ≠ a := fun h => by subst h; exact lt_irrefl _ hab
        simp [ev_apply, hb]
      · simp [ev_apply, ha]
    · rfl
  simp only [o] at e1 e2 e3
  rw [e1, e2, e3, add_zero, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rcases lt_trichotomy ((Fintype.equivFin I) v).val ((Fintype.equivFin I) w).val with h1 | h1 | h1
  · rw [if_pos h1, if_neg (not_lt.mpr h1.le), add_zero]
  · have : v = w := (Fintype.equivFin I).injective (Fin.ext h1)
    subst this
    simp [hdiag]
  · rw [if_neg (not_lt.mpr h1.le), if_pos h1, zero_add]

/-- the generator is the conjugated single flip. -/
theorem x8_gen_DX (A : Matrix I I F2) (hsym : ∀ a b, A a b = A b a) (hdiag : ∀ a, A a a = 0)
    (v : I) : signalGenerator A v = x8D A * x8X (ev v) * x8D A := by
  ext s s'
  simp only [x8D, diagonal_mul, mul_diagonal, x8X, of_apply, signalGenerator, tensorOps]
  by_cases h : bv s = bv s' + ev v
  · rw [if_pos h, mul_one]
    have h' : bv s' = bv s + ev v := by
      rw [h, add_assoc]
      have : ev v + ev v = 0 := by
        funext w; simp only [Pi.add_apply, ev_apply, Pi.zero_apply]; split_ifs <;> decide
      rw [this, add_zero]
    rw [x8_flip A hsym hdiag s s' v h', sgn_add, ← mul_assoc, sgn_sq, one_mul, sgn_sum]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hw := congrFun h' w
    simp only [bv, Pi.add_apply, ev_apply] at hw
    by_cases hwv : w = v
    · subst hwv
      rw [if_pos rfl, hdiag, zero_mul, sgn_zero]
      simp only [if_true] at hw
      have : s' w = !s w := by
        apply bit_inj; rw [hw, bit_not]
      rw [this]
      cases s w <;> simp [pauliX]
    · rw [if_neg hwv]
      simp only [hwv, if_false, add_zero] at hw
      have : s' w = s w := bit_inj hw
      rw [this]
      rcases x8_Z2' (A v w) with h0 | h1
      · rw [if_neg (by rw [h0]; decide), h0, zero_mul, sgn_zero]
        simp
      · rw [if_pos h1, h1, one_mul]
        cases s w <;> simp [pauliZ, sgn, bit]
  · rw [if_neg h, mul_zero, zero_mul]
    have : ∃ w, ¬ (bv s w = bv s' w + ev v w) := by
      by_contra hc; push Not at hc; exact h (funext hc)
    obtain ⟨w, hw⟩ := this
    refine Finset.prod_eq_zero (Finset.mem_univ w) ?_
    simp only [bv, ev_apply] at hw
    by_cases hwv : w = v
    · subst hwv
      rw [if_pos rfl]
      simp only [if_true] at hw
      have : s' w = s w := by
        by_contra hne
        apply hw
        have : s' w = !s w := by cases hs : s w <;> cases hs' : s' w <;> simp_all
        rw [this, bit_not, add_assoc]
        have : (1 : ZMod 2) + 1 = 0 := by decide
        rw [this, add_zero]
      rw [this]
      cases s w <;> simp [pauliX]
    · rw [if_neg hwv]
      simp only [hwv, if_false, add_zero] at hw
      have hne : s w ≠ s' w := fun h => hw (by rw [h])
      split_ifs
      · cases hs : s w <;> cases hs' : s' w <;> simp_all [pauliZ]
      · rw [one_apply_ne hne]

theorem x8_stab_DX (A : Matrix I I F2) (hsym : ∀ a b, A a b = A b a) (hdiag : ∀ a, A a a = 0)
    (x : I → F2) : signalStabilizer A x = x8D A * x8X x * x8D A := by
  let e := Fintype.equivFin I
  have gen : ∀ n (Fs : Fin n → Op (I → Bool)) (ys : Fin n → I → ZMod 2),
      (∀ i, Fs i = x8D A * x8X (ys i) * x8D A) →
      (List.ofFn Fs).prod = x8D A * x8X (∑ i, ys i) * x8D A := by
    intro n
    induction n with
    | zero =>
      intro Fs ys _
      simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
      rw [x8_X_zero, Matrix.mul_one, x8_D_sq]
    | succ n ih =>
      intro Fs ys h
      rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ, ih _ _ (fun i => h i.succ), h 0]
      have : x8D A * x8X (ys 0) * x8D A * (x8D A * x8X (∑ i : Fin n, ys i.succ) * x8D A) =
          x8D A * (x8X (ys 0) * (x8D A * x8D A) * x8X (∑ i : Fin n, ys i.succ)) * x8D A := by
        simp only [Matrix.mul_assoc]
      rw [this, x8_D_sq, Matrix.mul_one, x8_X_mul]
  have hx : x = ∑ a : Fin (Fintype.card I), x (e.symm a) • ev (e.symm a) := by
    rw [Equiv.sum_comp e.symm (fun v => x v • (ev v : I → ZMod 2))]
    funext w
    simp [Finset.sum_apply, ev_apply]
  unfold signalStabilizer
  conv_rhs => rw [hx]
  apply gen
  intro i
  dsimp only
  split_ifs with h
  · rw [h, one_smul, x8_gen_DX A hsym hdiag]
  · have h0 : x (e.symm i) = 0 := (x8_Z2' _).resolve_right h
    rw [h0, zero_smul, x8_X_zero, Matrix.mul_one, x8_D_sq]

end X8P22


open scoped ComplexConjugate ComplexOrder Matrix Kronecker

noncomputable section

namespace X8P22
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22 Matrix

variable {I : Type} [Fintype I] [DecidableEq I]

theorem sgn_conj (t : ZMod 2) : conj (sgn t) = sgn t := by
  simp only [sgn]; split_ifs <;> simp

theorem x8_charsum (c : I → ZMod 2) :
    ∑ n : I → Bool, sgn (∑ b, c b * bit (n b)) = if c = 0 then (2 : ℂ) ^ Fintype.card I else 0 := by
  simp only [sgn_sum]
  rw [← Fintype.prod_sum (fun b t => sgn (c b * bit t))]
  simp only [Fintype.sum_bool, bit, if_true, mul_one, mul_zero, sgn_zero, Bool.false_eq_true,
    if_false]
  split_ifs with hc
  · subst hc
    simp [sgn_zero, Finset.prod_const, Finset.card_univ]
    norm_num
  · obtain ⟨b, hb⟩ : ∃ b, c b ≠ 0 := by
      by_contra h; push Not at h; exact hc (funext h)
    refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
    have : c b = 1 := (x8_Z2' _).resolve_left hb
    rw [this]; simp [sgn]

theorem x8_beta (B : I → I → ZMod 2) (x y n : I → ZMod 2) :
    (∑ a, ∑ b, x a * B a b * n b) + (∑ a, ∑ b, y a * B a b * n b) =
      ∑ b, (∑ a, B a b * (x a + y a)) * n b := by
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

theorem x8_gv (G : CutGraph I) (p : (I → Bool) × (I → Bool)) :
    (graphVector G) p = ((2 : ℂ) ^ Fintype.card I)⁻¹ * sgn (quadratic G.AS p.1 +
      (∑ a, ∑ b, bit (p.1 a) * G.B a b * bit (p.2 b)) + quadratic G.AN p.2) := rfl

theorem x8_trR (G : CutGraph I) (s s' : I → Bool) :
    traceRight (pureDensity (graphVector G)) s s' =
      ((2 : ℂ) ^ Fintype.card I)⁻¹ * (sgn (quadratic G.AS s) * sgn (quadratic G.AS s')) *
        (if G.B.transpose.mulVec (bv s + bv s') = 0 then 1 else 0) := by
  simp only [traceRight, pureDensity, of_apply, x8_gv, map_mul, map_inv₀, map_pow,
    sgn_conj]
  have hc2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  simp only [hc2]
  have key : ∀ n : I → Bool,
      sgn (quadratic G.AS s + (∑ a, ∑ b, bit (s a) * G.B a b * bit (n b)) + quadratic G.AN n) *
      sgn (quadratic G.AS s' + (∑ a, ∑ b, bit (s' a) * G.B a b * bit (n b)) + quadratic G.AN n) =
      (sgn (quadratic G.AS s) * sgn (quadratic G.AS s')) *
        sgn (∑ b, G.B.transpose.mulVec (bv s + bv s') b * bit (n b)) := by
    intro n
    have hβ : (∑ a, ∑ b, bit (s a) * G.B a b * bit (n b)) + (∑ a, ∑ b, bit (s' a) * G.B a b * bit (n b))
        = ∑ b, G.B.transpose.mulVec (bv s + bv s') b * bit (n b) := by
      have hm : ∀ b, G.B.transpose.mulVec (bv s + bv s') b = ∑ a, G.B a b * (bit (s a) + bit (s' a)) :=
        fun b => rfl
      simp only [hm]
      exact x8_beta (fun a b => G.B a b) _ _ _
    rw [← hβ]
    simp only [sgn_add]
    have := sgn_sq (quadratic G.AN n)
    linear_combination (sgn (quadratic G.AS s) * sgn (∑ a, ∑ b, bit (s a) * G.B a b * bit (n b)) *
      sgn (quadratic G.AS s') * sgn (∑ a, ∑ b, bit (s' a) * G.B a b * bit (n b))) * this
  have e : ∀ n : I → Bool,
      ((2 : ℂ) ^ Fintype.card I)⁻¹ * sgn (quadratic G.AS s +
        (∑ a, ∑ b, bit (s a) * G.B a b * bit (n b)) + quadratic G.AN n) *
      (((2 : ℂ) ^ Fintype.card I)⁻¹ * sgn (quadratic G.AS s' +
        (∑ a, ∑ b, bit (s' a) * G.B a b * bit (n b)) + quadratic G.AN n)) =
      ((2 : ℂ) ^ Fintype.card I)⁻¹ * ((2 : ℂ) ^ Fintype.card I)⁻¹ *
        ((sgn (quadratic G.AS s) * sgn (quadratic G.AS s')) *
          sgn (∑ b, G.B.transpose.mulVec (bv s + bv s') b * bit (n b))) := by
    intro n; rw [← key n]; ring
  simp only [e]
  rw [← Finset.mul_sum, ← Finset.mul_sum, x8_charsum]
  have h2 : ((2 : ℂ) ^ Fintype.card I) ≠ 0 := pow_ne_zero _ two_ne_zero
  split_ifs
  · field_simp
  · simp

/-- stabilizer entries. -/
theorem x8_stab_entry (A : Matrix I I F2) (hsym : ∀ a b, A a b = A b a) (hdiag : ∀ a, A a a = 0)
    (x : I → F2) (s s' : I → Bool) :
    signalStabilizer A x s s' = sgn (quadratic A s) * sgn (quadratic A s') *
      (if x = bv s + bv s' then 1 else 0) := by
  rw [x8_stab_DX A hsym hdiag]
  simp only [x8D, diagonal_mul, mul_diagonal, x8X, of_apply]
  have : (bv s = bv s' + x) ↔ (x = bv s + bv s') := by
    have hz : bv s' + bv s' = 0 := funext fun w => by
      rcases x8_Z2' (bv s' w) with h | h <;> simp [h] <;> decide
    constructor
    · intro h; rw [h, add_comm (bv s') x, add_assoc, hz, add_zero]
    · intro h; rw [h, add_comm (bv s) (bv s'), ← add_assoc, hz, zero_add]
  by_cases h : x = bv s + bv s'
  · rw [if_pos (this.mpr h), if_pos h]; ring
  · rw [if_neg (fun h' => h (this.mp h')), if_neg h]; ring

end X8P22


open scoped ComplexConjugate ComplexOrder Matrix Kronecker
open Matrix Polynomial

noncomputable section

namespace X8P22
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22

theorem x8_pow {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (W : Matrix ι κ ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) (d : κ → ℂ)
    (h : A = W * diagonal d * Wᴴ) (n : ℕ) : A ^ n = W * diagonal (d ^ n) * Wᴴ := by
  induction n with
  | zero => simp [hW2]
  | succ n ih =>
    rw [pow_succ, ih, h]
    have : W * diagonal (d ^ n) * Wᴴ * (W * diagonal d * Wᴴ) =
        W * (diagonal (d ^ n) * (Wᴴ * W) * diagonal d) * Wᴴ := by
      simp only [Matrix.mul_assoc]
    rw [this, hW1, Matrix.mul_one, diagonal_mul_diagonal, pow_succ]
    rfl

theorem x8_aeval {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (W : Matrix ι κ ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) (d : κ → ℝ)
    (h : A = W * diagonal (fun k => (d k : ℂ)) * Wᴴ) (p : ℝ[X]) :
    aeval A p = W * diagonal (fun k => ((p.eval (d k) : ℝ) : ℂ)) * Wᴴ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
    congr 3; ext k; simp
  | monomial n c =>
    rw [aeval_monomial, x8_pow A W hW1 hW2 _ h n]
    simp only [eval_monomial]
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_mul, ← Matrix.smul_mul,
      ← Matrix.mul_smul, ← diagonal_smul]
    congr 3; ext k; simp [Pi.pow_apply]

theorem x8_trace_cfc {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (W : Matrix ι κ ℂ) (hW1 : Wᴴ * W = 1)
    (hW2 : W * Wᴴ = 1) (d : κ → ℝ)
    (h : A = W * diagonal (fun k => (d k : ℂ)) * Wᴴ) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ k, ((f (d k) : ℝ) : ℂ) := by
  classical
  let S : Finset ℝ := Finset.univ.image d ∪ Finset.univ.image hA.eigenvalues
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have h1 : cfc f A = cfc (fun x => p.eval x) A := by
    apply cfc_congr
    intro x hx
    rw [hA.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))).symm
  rw [h1, cfc_polynomial p A, x8_aeval A W hW1 hW2 d h p, Matrix.trace_mul_cycle, hW1,
    Matrix.one_mul, trace_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))]


theorem x8_spec {α : Type*} [Fintype α] [DecidableEq α] {A : Matrix α α ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix α α ℂ) *
      diagonal (fun k => ((hA.eigenvalues k : ℝ) : ℂ)) * (hA.eigenvectorUnitary : Matrix α α ℂ)ᴴ := by
  conv_lhs => rw [hA.spectral_theorem]
  rfl

theorem x8_U1 {α : Type*} [Fintype α] [DecidableEq α] {A : Matrix α α ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix α α ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix α α ℂ) = 1 :=
  Unitary.coe_star_mul_self _

theorem x8_U2 {α : Type*} [Fintype α] [DecidableEq α] {A : Matrix α α ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix α α ℂ) * (hA.eigenvectorUnitary : Matrix α α ℂ)ᴴ = 1 :=
  Unitary.coe_mul_star_self _

theorem x8_ent_eig {α : Type*} [Fintype α] [DecidableEq α] {A : Matrix α α ℂ} (hA : A.IsHermitian) :
    vnEntropy A = -∑ k, hA.eigenvalues k * Real.logb 2 (hA.eigenvalues k) := by
  unfold vnEntropy
  rw [x8_trace_cfc A hA _ (x8_U1 hA) (x8_U2 hA) _ (x8_spec hA)]
  simp [Complex.re_sum]

theorem x8_sum_eig {α : Type*} [Fintype α] [DecidableEq α] {A : Matrix α α ℂ} (hA : A.IsHermitian)
    (ht : A.trace = 1) : ∑ k, hA.eigenvalues k = 1 := by
  have := hA.trace_eq_sum_eigenvalues
  rw [ht] at this
  have h2 := congrArg Complex.re this
  simpa [Complex.re_sum] using h2.symm

theorem x8_scaled {α : Type} [Fintype α] [DecidableEq α] {A : Matrix α α ℂ} (hA : A.IsHermitian)
    (c : ℝ) (hc : 0 < c) (h2 : A * A = (c : ℂ) • A) (ht : A.trace = 1) :
    (A.rank : ℝ) * c = 1 ∧ vnEntropy A = -Real.logb 2 c := by
  set U := (hA.eigenvectorUnitary : Matrix α α ℂ)
  have e1 : Uᴴ * A * U = diagonal (fun k => ((hA.eigenvalues k : ℝ) : ℂ)) := by
    conv_lhs => rw [x8_spec hA]
    have : Uᴴ * (U * diagonal (fun k => ((hA.eigenvalues k : ℝ) : ℂ)) * Uᴴ) * U =
        (Uᴴ * U) * diagonal (fun k => ((hA.eigenvalues k : ℝ) : ℂ)) * (Uᴴ * U) := by
      simp only [Matrix.mul_assoc]
    rw [this, x8_U1 hA, Matrix.one_mul, Matrix.mul_one]
  have e2 : Uᴴ * (A * A) * U = (Uᴴ * A * U) * (Uᴴ * A * U) := by
    have : (Uᴴ * A * U) * (Uᴴ * A * U) = Uᴴ * A * (U * Uᴴ) * A * U := by
      simp only [Matrix.mul_assoc]
    rw [this, x8_U2 hA, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  have hev : ∀ k, hA.eigenvalues k = 0 ∨ hA.eigenvalues k = c := by
    intro k
    have := congrFun (congrFun (e2.symm.trans (by rw [h2])) k) k
    rw [e1, diagonal_mul_diagonal, Matrix.mul_smul, Matrix.smul_mul, e1] at this
    simp only [diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul] at this
    have h' : hA.eigenvalues k * hA.eigenvalues k = c * hA.eigenvalues k := by
      exact_mod_cast this
    rcases mul_eq_mul_right_iff.mp h' with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hs := x8_sum_eig hA ht
  constructor
  · rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    have : ∑ k, hA.eigenvalues k = ∑ k, (if hA.eigenvalues k ≠ 0 then c else 0) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rcases hev k with h | h
      · simp [h]
      · rw [if_pos (by rw [h]; exact hc.ne'), h]
    rw [this, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul] at hs
    exact hs
  · rw [x8_ent_eig hA]
    have : ∑ k, hA.eigenvalues k * Real.logb 2 (hA.eigenvalues k) =
        ∑ k, hA.eigenvalues k * Real.logb 2 c := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rcases hev k with h | h <;> simp [h]
    rw [this, ← Finset.sum_mul, hs, one_mul]

end X8P22


open scoped ComplexConjugate ComplexOrder Matrix Kronecker
open Matrix

noncomputable section

namespace X8P22
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22

local instance x8iK {I : Type} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

variable {I : Type} [Fintype I] [DecidableEq I]

theorem x8_memK (G : CutGraph I) (u : I → F2) : u ∈ cutKernel G ↔ G.B.transpose.mulVec u = 0 := by
  unfold cutKernel
  rw [LinearMap.mem_ker, mulVecLin_apply]

theorem x8_conj1 (G : CutGraph I) :
    traceRight (pureDensity (graphVector G)) =
      ((2 : ℂ) ^ Fintype.card I)⁻¹ • ∑ x : cutKernel G, signalStabilizer G.AS x.1 := by
  ext s s'
  rw [x8_trR, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  simp only [x8_stab_entry G.AS G.symS G.diagS]
  rw [← Finset.mul_sum, mul_assoc]
  congr 2
  by_cases hu : bv s + bv s' ∈ cutKernel G
  · rw [if_pos ((x8_memK G _).mp hu)]
    rw [Finset.sum_eq_single (⟨bv s + bv s', hu⟩ : cutKernel G)]
    · simp
    · intro y _ hy
      rw [if_neg]
      intro h; apply hy; exact Subtype.ext h
    · simp
  · rw [if_neg (fun h => hu ((x8_memK G _).mpr h))]
    refine (Finset.sum_eq_zero fun y _ => ?_).symm
    rw [if_neg]
    intro h; apply hu; rw [← h]; exact y.2

theorem x8_cardK (G : CutGraph I) :
    G.B.rank ≤ Fintype.card I ∧
      Fintype.card (cutKernel G) = 2 ^ (Fintype.card I - G.B.rank) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (G.B.transpose.mulVecLin)
  rw [Module.finrank_fintype_fun_eq_card] at h1
  have h2 : Module.finrank F2 (LinearMap.range G.B.transpose.mulVecLin) = G.B.rank := by
    rw [← rank_transpose]; rfl
  rw [h2] at h1
  refine ⟨by omega, ?_⟩
  rw [Module.card_eq_pow_finrank (K := F2) (V := cutKernel G), ZMod.card]
  congr 1
  unfold cutKernel
  omega

theorem x8_S_mul (A : Matrix I I F2) (hsym : ∀ a b, A a b = A b a) (hdiag : ∀ a, A a a = 0)
    (x y : I → F2) : signalStabilizer A x * signalStabilizer A y = signalStabilizer A (x + y) := by
  rw [x8_stab_DX A hsym hdiag, x8_stab_DX A hsym hdiag, x8_stab_DX A hsym hdiag]
  have : x8D A * x8X x * x8D A * (x8D A * x8X y * x8D A) =
      x8D A * (x8X x * (x8D A * x8D A) * x8X y) * x8D A := by simp only [Matrix.mul_assoc]
  rw [this, x8_D_sq, Matrix.mul_one, x8_X_mul]

theorem x8_S_H (A : Matrix I I F2) (hsym : ∀ a b, A a b = A b a) (hdiag : ∀ a, A a a = 0)
    (x : I → F2) : (signalStabilizer A x)ᴴ = signalStabilizer A x := by
  rw [x8_stab_DX A hsym hdiag, conjTranspose_mul, conjTranspose_mul, x8_D_H, x8_X_H,
    Matrix.mul_assoc]

theorem x8_P_def (G : CutGraph I) :
    graphProjector G = ((Fintype.card (cutKernel G) : ℂ))⁻¹ •
      ∑ x : cutKernel G, signalStabilizer G.AS x.1 := rfl

theorem x8_P_sq (G : CutGraph I) : graphProjector G * graphProjector G = graphProjector G := by
  rw [x8_P_def, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Finset.sum_mul_sum]
  simp only [x8_S_mul G.AS G.symS G.diagS]
  have : ∀ x : cutKernel G, ∑ y : cutKernel G, signalStabilizer G.AS (x.1 + y.1) =
      ∑ z : cutKernel G, signalStabilizer G.AS z.1 := by
    intro x
    exact Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun y => by simp)
  simp only [this, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hK : (Fintype.card (cutKernel G) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  congr 1
  field_simp

theorem x8_P_H (G : CutGraph I) : (graphProjector G)ᴴ = graphProjector G := by
  rw [x8_P_def, conjTranspose_smul, conjTranspose_sum]
  simp only [x8_S_H G.AS G.symS G.diagS]
  congr 1
  simp

theorem x8_conj2 (G : CutGraph I) :
    traceRight (pureDensity (graphVector G)) = ((2 : ℂ) ^ G.B.rank)⁻¹ • graphProjector G := by
  rw [x8_conj1, x8_P_def, smul_smul]
  congr 1
  obtain ⟨hr, hc⟩ := x8_cardK G
  rw [hc]
  push_cast
  rw [← mul_inv, ← pow_add, Nat.add_sub_cancel' hr]

theorem x8_trace1 (G : CutGraph I) : (traceRight (pureDensity (graphVector G))).trace = 1 := by
  simp only [trace, diag, x8_trR]
  have : ∀ s : I → Bool, bv s + bv s = 0 := fun s => funext fun w => by
    rcases x8_Z2' (bv s w) with h | h <;> simp [h] <;> decide
  simp only [this, mulVec_zero, if_true, mul_one, sgn_sq]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul]
  push_cast
  field_simp

end X8P22


open scoped ComplexConjugate ComplexOrder Matrix Kronecker
open Matrix

noncomputable section

namespace X8P22
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22

local instance x8iK' {I : Type} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

theorem x8_main (nu : ℕ) (hnu : 1 ≤ nu) (G : CutGraph (Fin nu)) :
    traceRight (pureDensity (graphVector G)) =
      ((2 : ℂ)^nu)⁻¹ • ∑ x : cutKernel G, signalStabilizer G.AS x.1 ∧
    traceRight (pureDensity (graphVector G)) = ((2 : ℂ)^G.B.rank)⁻¹ • graphProjector G ∧
    graphProjector G * graphProjector G = graphProjector G ∧
    (graphProjector G)ᴴ = graphProjector G ∧ (graphProjector G).rank = 2^G.B.rank ∧
    (traceRight (pureDensity (graphVector G))).rank = 2^G.B.rank ∧
    vnEntropy (traceRight (pureDensity (graphVector G))) = G.B.rank := by
  have c1 := x8_conj1 G
  rw [Fintype.card_fin] at c1
  have c2 := x8_conj2 G
  have hP2 := x8_P_sq G
  have hPH := x8_P_H G
  set ρ := traceRight (pureDensity (graphVector G))
  set P := graphProjector G
  set r := G.B.rank
  have hcR : (((((2 : ℝ) ^ r)⁻¹ : ℝ)) : ℂ) = ((2 : ℂ) ^ r)⁻¹ := by push_cast; rfl
  have hρH : ρ.IsHermitian := by
    rw [c2, IsHermitian, conjTranspose_smul, hPH, ← hcR, Complex.star_def, Complex.conj_ofReal]
  have hρ2 : ρ * ρ = ((((2 : ℝ) ^ r)⁻¹ : ℝ) : ℂ) • ρ := by
    rw [hcR, c2, Matrix.smul_mul, Matrix.mul_smul, hP2, smul_smul]
  obtain ⟨hrk, hent⟩ := x8_scaled hρH (((2 : ℝ) ^ r)⁻¹) (by positivity) hρ2 (x8_trace1 G)
  have hrank : ρ.rank = 2 ^ r := by
    have h2 : (2 : ℝ) ^ r ≠ 0 := by positivity
    have : (ρ.rank : ℝ) = 2 ^ r := by
      field_simp at hrk; linarith
    exact_mod_cast this
  refine ⟨c1, c2, hP2, hPH, ?_, hrank, ?_⟩
  · rw [← hrank, c2, rank_smul_of_mem_nonZeroDivisors]
    exact mem_nonZeroDivisors_of_ne_zero (inv_ne_zero (pow_ne_zero _ two_ne_zero))
  · rw [hent, Real.logb_inv, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    simp

end X8P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

theorem x8_target (nu : ℕ) (hnu : 1 ≤ nu) (G : CutGraph (Fin nu)) :
    traceRight (pureDensity (graphVector G)) =
      ((2 : ℂ)^nu)⁻¹ • ∑ x : cutKernel G, signalStabilizer G.AS x.1 ∧
    traceRight (pureDensity (graphVector G)) = ((2 : ℂ)^G.B.rank)⁻¹ • graphProjector G ∧
    graphProjector G * graphProjector G = graphProjector G ∧
    (graphProjector G)ᴴ = graphProjector G ∧ (graphProjector G).rank = 2^G.B.rank ∧
    (traceRight (pureDensity (graphVector G))).rank = 2^G.B.rank ∧
    vnEntropy (traceRight (pureDensity (graphVector G))) = G.B.rank :=
  X8P22.x8_main nu hnu G

end

end QAlgorithms.Papers.Independent.Information100.P22

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22 in
local instance x8topK {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22 in
/-- Lemma S3, PDF p.29: signed expansion, projector, rank, and entropy. -/
theorem solution (nu : ℕ) (hnu : 1 ≤ nu) (G : CutGraph (Fin nu)) :
    traceRight (pureDensity (graphVector G)) =
      ((2 : ℂ)^nu)⁻¹ • ∑ x : cutKernel G, signalStabilizer G.AS x.1 ∧
    traceRight (pureDensity (graphVector G)) = ((2 : ℂ)^G.B.rank)⁻¹ • graphProjector G ∧
    graphProjector G * graphProjector G = graphProjector G ∧
    (graphProjector G)ᴴ = graphProjector G ∧ (graphProjector G).rank = 2^G.B.rank ∧
    (traceRight (pureDensity (graphVector G))).rank = 2^G.B.rank ∧
    vnEntropy (traceRight (pureDensity (graphVector G))) = G.B.rank :=
  x8_target nu hnu G
