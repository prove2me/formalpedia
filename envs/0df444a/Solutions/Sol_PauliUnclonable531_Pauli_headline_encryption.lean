-- Prove2me | solution 1 for PauliUnclonable531.Pauli.headline_encryption
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T09:04:20.19069+00:00
-- url     : https://prove2.me/submissions/1cb5210a-af1e-4b58-bc1d-0bedbbb42b6e

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Game
import Definitions.Def_PauliUnclonable531_Pauli_Ensemble
import Theorems.Thm_PauliUnclonable531_Pauli_security
import Theorems.Thm_PauliUnclonable531_Pauli_correctness
import Theorems.Thm_PauliUnclonable531_Pauli_preparation
import Theorems.Thm_PauliUnclonable531_Pauli_pauli_bridges
import Theorems.Thm_PauliUnclonable531_Pauli_encryption_execution
import Theorems.Thm_PauliUnclonable531_Pauli_decryption_execution
import Theorems.Thm_PauliUnclonable531_Pauli_resource_counts

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli.HeadlineAux

open PauliUnclonable531.Pauli

/-! ## Single-qubit gates -/

lemma sqrt2_inv_sq : ((Real.sqrt 2 : ℂ))⁻¹ ^ 2 = 1/2 := by
  rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

lemma gate_facts (g : Gate) : (gateMatrix g).conjTranspose * gateMatrix g = 1 ∧
    ∀ p : Fin 4, ∃ q : Fin 4, ∃ b : Fin 2,
      gateMatrix g * QMaxCutSDP.Rounding.pauli p * (gateMatrix g).conjTranspose =
        sign b • QMaxCutSDP.Rounding.pauli q := by
  have hconj : (starRingEnd ℂ) ((Real.sqrt 2 : ℂ))⁻¹ = ((Real.sqrt 2 : ℂ))⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal]
  cases g with
  | X =>
    refine ⟨?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [gateMatrix, QMaxCutSDP.Rounding.pauli, Matrix.mul_apply, Fin.sum_univ_two]
    · intro p
      fin_cases p
      · exact ⟨0, 0, by ext i j; fin_cases i <;> fin_cases j <;>
          simp [gateMatrix, QMaxCutSDP.Rounding.pauli, Matrix.mul_apply, Fin.sum_univ_two, sign]⟩
      · exact ⟨1, 0, by ext i j; fin_cases i <;> fin_cases j <;>
          simp [gateMatrix, QMaxCutSDP.Rounding.pauli, Matrix.mul_apply, Fin.sum_univ_two, sign]⟩
      · exact ⟨2, 1, by ext i j; fin_cases i <;> fin_cases j <;>
          simp [gateMatrix, QMaxCutSDP.Rounding.pauli, Matrix.mul_apply, Fin.sum_univ_two, sign]⟩
      · exact ⟨3, 1, by ext i j; fin_cases i <;> fin_cases j <;>
          simp [gateMatrix, QMaxCutSDP.Rounding.pauli, Matrix.mul_apply, Fin.sum_univ_two, sign]⟩
  | H =>
    refine ⟨?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [gateMatrix, Matrix.mul_apply, Fin.sum_univ_two, hconj] <;> (first | rfl | linear_combination (2:ℂ) * sqrt2_inv_sq | linear_combination (-2:ℂ) * sqrt2_inv_sq | linear_combination sqrt2_inv_sq | linear_combination (-1:ℂ) * sqrt2_inv_sq | linear_combination (2 * Complex.I) * sqrt2_inv_sq | linear_combination (-2 * Complex.I) * sqrt2_inv_sq)
    · intro p
      fin_cases p
      · exact ⟨0, 0, by ext i j; fin_cases i <;> fin_cases j <;>
          simp [gateMatrix, QMaxCutSDP.Rounding.pauli, Matrix.mul_apply, Fin.sum_univ_two, sign,
            hconj] <;> (first | rfl | linear_combination (2:ℂ) * sqrt2_inv_sq | linear_combination (-2:ℂ) * sqrt2_inv_sq | linear_combination sqrt2_inv_sq | linear_combination (-1:ℂ) * sqrt2_inv_sq | linear_combination (2 * Complex.I) * sqrt2_inv_sq | linear_combination (-2 * Complex.I) * sqrt2_inv_sq)⟩
      · exact ⟨3, 0, by ext i j; fin_cases i <;> fin_cases j <;>
          simp [gateMatrix, QMaxCutSDP.Rounding.pauli, Matrix.mul_apply, Fin.sum_univ_two, sign,
            hconj] <;> (first | rfl | linear_combination (2:ℂ) * sqrt2_inv_sq | linear_combination (-2:ℂ) * sqrt2_inv_sq | linear_combination sqrt2_inv_sq | linear_combination (-1:ℂ) * sqrt2_inv_sq | linear_combination (2 * Complex.I) * sqrt2_inv_sq | linear_combination (-2 * Complex.I) * sqrt2_inv_sq)⟩
      · exact ⟨2, 1, by ext i j; fin_cases i <;> fin_cases j <;>
          simp [gateMatrix, QMaxCutSDP.Rounding.pauli, Matrix.mul_apply, Fin.sum_univ_two, sign,
            hconj] <;> (first | rfl | linear_combination (2:ℂ) * sqrt2_inv_sq | linear_combination (-2:ℂ) * sqrt2_inv_sq | linear_combination sqrt2_inv_sq | linear_combination (-1:ℂ) * sqrt2_inv_sq | linear_combination (2 * Complex.I) * sqrt2_inv_sq | linear_combination (-2 * Complex.I) * sqrt2_inv_sq)⟩
      · exact ⟨1, 0, by ext i j; fin_cases i <;> fin_cases j <;>
          simp [gateMatrix, QMaxCutSDP.Rounding.pauli, Matrix.mul_apply, Fin.sum_univ_two, sign,
            hconj] <;> (first | rfl | linear_combination (2:ℂ) * sqrt2_inv_sq | linear_combination (-2:ℂ) * sqrt2_inv_sq | linear_combination sqrt2_inv_sq | linear_combination (-1:ℂ) * sqrt2_inv_sq | linear_combination (2 * Complex.I) * sqrt2_inv_sq | linear_combination (-2 * Complex.I) * sqrt2_inv_sq)⟩
  | S =>
    refine ⟨?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [gateMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    · intro p
      fin_cases p
      · exact ⟨0, 0, by ext i j; fin_cases i <;> fin_cases j <;>
          simp [gateMatrix, QMaxCutSDP.Rounding.pauli, Matrix.mul_apply, Fin.sum_univ_two, sign]⟩
      · exact ⟨2, 0, by ext i j; fin_cases i <;> fin_cases j <;>
          simp [gateMatrix, QMaxCutSDP.Rounding.pauli, Matrix.mul_apply, Fin.sum_univ_two, sign]⟩
      · exact ⟨1, 1, by ext i j; fin_cases i <;> fin_cases j <;>
          simp [gateMatrix, QMaxCutSDP.Rounding.pauli, Matrix.mul_apply, Fin.sum_univ_two, sign]⟩
      · exact ⟨3, 0, by ext i j; fin_cases i <;> fin_cases j <;>
          simp [gateMatrix, QMaxCutSDP.Rounding.pauli, Matrix.mul_apply, Fin.sum_univ_two, sign]⟩

/-! ## Keys -/

lemma card_key (n : ℕ) : Fintype.card (Key n) = 4^n - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_prod]
  simp [Bits, ← mul_pow]

lemma keyEncode_injective (n : ℕ) : Function.Injective (@keyEncode n) := by
  intro k l h
  apply Subtype.ext
  have h1 : k.val.1 = l.val.1 := by
    funext i
    have := congrFun h (Fin.castAdd n i)
    rwa [keyEncode, keyEncode, Fin.append_left, Fin.append_left] at this
  have h2 : k.val.2 = l.val.2 := by
    funext i
    have := congrFun h (Fin.natAdd n i)
    rwa [keyEncode, keyEncode, Fin.append_right, Fin.append_right] at this
  exact Prod.ext h1 h2

/-! ## Pauli operators -/

lemma qubitPauli_hermitian (a : Fin 4) (x y : Fin 2) :
    star (QMaxCutSDP.Rounding.pauli a y x) = QMaxCutSDP.Rounding.pauli a x y := by
  fin_cases a <;> fin_cases x <;> fin_cases y <;> simp [QMaxCutSDP.Rounding.pauli]

lemma pauli_isHermitian {n : ℕ} (k : Label n) : (pauli k).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, pauli, QMaxCutSDP.Rounding.pauliString]
  rw [star_prod]
  exact Finset.prod_congr rfl fun i _ => qubitPauli_hermitian _ _ _

lemma qubitPauli_trace (a : Fin 4) (ha : a ≠ 0) :
    ∑ x : Fin 2, QMaxCutSDP.Rounding.pauli a x x = 0 := by
  fin_cases a
  · exact absurd rfl ha
  all_goals simp [QMaxCutSDP.Rounding.pauli, Fin.sum_univ_two]

lemma pauli_trace {n : ℕ} (k : Label n) (hk : k ≠ (0, 0)) : (pauli k).trace = 0 := by
  have hex : ∃ j, localLabel (k.1 j) (k.2 j) ≠ 0 := by
    by_contra hne
    push_neg at hne
    apply hk
    have h1 : ∀ j, k.1 j = 0 ∧ k.2 j = 0 := by
      intro j
      have := hne j
      revert this
      unfold localLabel
      generalize k.1 j = x
      generalize k.2 j = z
      fin_cases x <;> fin_cases z <;> simp
    exact Prod.ext (funext fun j => (h1 j).1) (funext fun j => (h1 j).2)
  obtain ⟨j, hj⟩ := hex
  simp only [Matrix.trace, Matrix.diag, pauli, QMaxCutSDP.Rounding.pauliString]
  rw [← Fintype.prod_sum (fun i (x : Fin 2) =>
    QMaxCutSDP.Rounding.pauli (localLabel (k.1 i) (k.2 i)) x x)]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (qubitPauli_trace _ hj)

lemma pauli_mul_self {n : ℕ} (k : Label n) : pauli k * pauli k = 1 := (pauli_bridges n k).1

/-- `1 + P` is positive semidefinite for a Hermitian involution `P`. -/
lemma one_add_psd {A : Type} [Fintype A] [DecidableEq A] (P : Op A) (hP : P.IsHermitian)
    (hPP : P * P = 1) : (1 + P).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (1 + P)
  have heq : (1 + P).conjTranspose * (1 + P) = (2 : ℝ) • (1 + P) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hP.eq]
    simp only [add_mul, mul_add, hPP, one_mul, mul_one, two_smul]
    abel
  rw [heq] at h
  have := h.smul (show (0 : ℝ) ≤ (2 : ℝ)⁻¹ by norm_num)
  rwa [smul_smul, inv_mul_cancel₀ (by norm_num), one_smul] at this

lemma one_add_sign_psd {A : Type} [Fintype A] [DecidableEq A] (P : Op A) (hP : P.IsHermitian)
    (hPP : P * P = 1) (m : Fin 2) : (1 + sign m • P).PosSemidef := by
  fin_cases m
  · simpa [sign] using one_add_psd P hP hPP
  · have := one_add_psd (-P) hP.neg (by rw [neg_mul_neg, hPP])
    simpa [sign, ← sub_eq_add_neg] using this

lemma ciphertext_density {n : ℕ} (k : Key n) (m : Fin 2) : Density (ciphertext k m) := by
  refine ⟨?_, ?_⟩
  · have h := (one_add_sign_psd (pauli k.val) (pauli_isHermitian _) (pauli_mul_self _) m).smul
      (show (0 : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹ by positivity)
    have heq : ((2 : ℝ) ^ n)⁻¹ • (1 + sign m • pauli k.val) = ciphertext k m := by
      rw [ciphertext, ← Complex.coe_smul]
      push_cast
      rfl
    rwa [heq] at h
  · rw [ciphertext, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul,
      pauli_trace k.val k.property, Matrix.trace_one]
    simp [Bits]

lemma decryptEffect_psd {n : ℕ} (k : Key n) (m : Fin 2) : (decryptEffect k m).PosSemidef := by
  have h := (one_add_sign_psd (pauli k.val) (pauli_isHermitian _) (pauli_mul_self _) m).smul
    (show (0 : ℝ) ≤ (1/2 : ℝ) by norm_num)
  have heq : (1/2 : ℝ) • (1 + sign m • pauli k.val) = decryptEffect k m := by
    rw [decryptEffect, ← Complex.coe_smul]
    push_cast
    rfl
  rwa [heq] at h

lemma decryptEffect_sum {n : ℕ} (k : Key n) : (∑ m, decryptEffect k m) = 1 := by
  simp only [Fin.sum_univ_two, decryptEffect, sign]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, one_smul]
  rw [← smul_add]
  rw [show (1 + pauli k.val + (1 + -pauli k.val) : Op (Bits n)) = (2 : ℂ) • 1 by
    rw [two_smul]; abel]
  rw [smul_smul]
  norm_num

/-! ## The general game -/

lemma channel_psd {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (Φ : Op I →ₗ[ℂ] Op J) (hΦ : WildeQIT.EntBreaking.IsQuantumChannel Φ) {X : Op I}
    (hX : X.PosSemidef) : (Φ X).PosSemidef := by
  have h := hΦ.1 1 (X.submatrix Prod.snd Prod.snd) (hX.submatrix _)
  have heq : Φ X = (QAlgorithms.idTensorSuperop (R := Fin 1) Φ
      (X.submatrix Prod.snd Prod.snd)).submatrix (fun j => ((0 : Fin 1), j))
        (fun j => ((0 : Fin 1), j)) := by
    rfl
  rw [heq]
  exact h.submatrix _

lemma born_nonneg {A : Type} [Fintype A] [DecidableEq A] {Q ρ : Op A} (hQ : Q.PosSemidef)
    (hρ : ρ.PosSemidef) : 0 ≤ born Q ρ := by
  open scoped MatrixOrder in
  obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.nonneg
  have h := (hQ.mul_mul_conjTranspose_same R).trace_nonneg
  unfold born
  rw [Matrix.star_eq_conjTranspose, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [← Matrix.mul_assoc]
  exact (Complex.nonneg_iff.mp h).1

lemma born_sub {A : Type} [Fintype A] (Q Q' ρ : Op A) :
    born (Q - Q') ρ = born Q ρ - born Q' ρ := by
  simp [born, Matrix.sub_mul, Matrix.trace_sub]

lemma born_add {A : Type} [Fintype A] (Q Q' ρ : Op A) :
    born (Q + Q') ρ = born Q ρ + born Q' ρ := by
  simp [born, Matrix.add_mul, Matrix.trace_add]

lemma kron_sub {l m p q : Type} (A : Matrix l m ℂ) (B₁ B₂ : Matrix p q ℂ) :
    Matrix.kronecker A (B₁ - B₂) = Matrix.kronecker A B₁ - Matrix.kronecker A B₂ := by
  ext ⟨_, _⟩ ⟨_, _⟩; simp [mul_sub]

lemma sub_kron {l m p q : Type} (A₁ A₂ : Matrix l m ℂ) (B : Matrix p q ℂ) :
    Matrix.kronecker (A₁ - A₂) B = Matrix.kronecker A₁ B - Matrix.kronecker A₂ B := by
  ext ⟨_, _⟩ ⟨_, _⟩; simp [sub_mul]

variable {n : ℕ} {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]

lemma success_effect_le_one (Q : Op B) (R : Op C) (hQ : Q.PosSemidef) (hQ' : (1 - Q).PosSemidef)
    (hR : R.PosSemidef) (hR' : (1 - R).PosSemidef) :
    (1 - (Matrix.kronecker Q R + Matrix.kronecker (1 - Q) (1 - R))).PosSemidef := by
  have heq : 1 - (Matrix.kronecker Q R + Matrix.kronecker (1 - Q) (1 - R)) =
      Matrix.kronecker Q (1 - R) + Matrix.kronecker (1 - Q) R := by
    have h11 : Matrix.kronecker (1 : Op B) (1 : Op C) = 1 := Matrix.one_kronecker_one
    simp only [kron_sub, sub_kron, h11]
    abel
  rw [heq]
  exact (hQ.kronecker hR').add (hQ'.kronecker hR)

lemma pairWin_same_le (a : Attack n B C) (m : Fin 2) :
    pairWin (explicitScheme n) a m m ≤ 1/2 := by
  unfold pairWin
  have hgen : ∀ k : Key n, (explicitScheme n).gen k = (Fintype.card (Key n) : ℝ)⁻¹ := fun _ => rfl
  have hterm : ∀ k : Key n, (∑ b : Fin 2,
      born (Matrix.kronecker (bobEffect a k b) (charlieEffect a k b))
        (a.split ((explicitScheme n).enc k (if b = 0 then m else m)))) ≤ 1 := by
    intro k
    set σ := a.split (ciphertext k m) with hσ
    have hρ := ciphertext_density k m
    have hσpsd : σ.PosSemidef := channel_psd a.split a.channel hρ.1
    have hσtr : σ.trace = 1 := by rw [hσ, a.channel.2, hρ.2]
    simp only [ite_self]
    change (∑ b : Fin 2, born (Matrix.kronecker (bobEffect a k b) (charlieEffect a k b)) σ) ≤ 1
    rw [Fin.sum_univ_two, ← born_add]
    have hle := born_nonneg (success_effect_le_one _ _ (a.bob_pos k) (a.bob_complement_pos k)
      (a.charlie_pos k) (a.charlie_complement_pos k)) hσpsd
    rw [born_sub] at hle
    have h1 : born 1 σ = 1 := by simp [born, hσtr]
    simp only [bobEffect, charlieEffect, MayersBC.binaryPOVM] at hle ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hle ⊢
    linarith
  have hK : (0 : ℝ) ≤ (Fintype.card (Key n) : ℝ)⁻¹ := by positivity
  calc (∑ k : Key n, (explicitScheme n).gen k * ((1/2 : ℝ) * ∑ b : Fin 2,
        born (Matrix.kronecker (bobEffect a k b) (charlieEffect a k b))
          (a.split ((explicitScheme n).enc k (if b = 0 then m else m)))))
      ≤ ∑ k : Key n, (Fintype.card (Key n) : ℝ)⁻¹ * ((1/2 : ℝ) * 1) := by
        apply Finset.sum_le_sum
        intro k _
        rw [hgen]
        gcongr
        exact hterm k
    _ ≤ 1/2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rcases Nat.eq_zero_or_pos (Fintype.card (Key n)) with h0 | hpos
        · rw [h0]; norm_num
        · rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hpos.ne')]
          norm_num

/-- Swapping both receivers' outcome labels. -/
def swapAttack (a : Attack n B C) : Attack n B C where
  split := a.split
  channel := a.channel
  bobZero k := 1 - a.bobZero k
  charlieZero k := 1 - a.charlieZero k
  bob_pos := a.bob_complement_pos
  bob_complement_pos k := by simpa using a.bob_pos k
  charlie_pos := a.charlie_complement_pos
  charlie_complement_pos k := by simpa using a.charlie_pos k

lemma pairWin_swap (a : Attack n B C) :
    pairWin (explicitScheme n) a 1 0 = win (swapAttack a) := by
  unfold win pairWin
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  simp only [Fin.sum_univ_two, bobEffect, charlieEffect, MayersBC.binaryPOVM, swapAttack]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_sub_cancel]
  simp
  ring

lemma bound_ge_half (n : ℕ) : (1/2 : ℝ) ≤ 1/2 + (1/2) * Real.sqrt ((2 : ℝ)^n / ((4 : ℝ)^n - 1)) := by
  have := Real.sqrt_nonneg ((2 : ℝ)^n / ((4 : ℝ)^n - 1))
  linarith

lemma pairWin_le [Nonempty B] [Nonempty C] (hn : 1 ≤ n) (a : Attack n B C) (u v : Fin 2) :
    pairWin (explicitScheme n) a u v ≤
      1/2 + (1/2) * Real.sqrt ((2 : ℝ)^n / ((4 : ℝ)^n - 1)) := by
  fin_cases u <;> fin_cases v
  · exact (pairWin_same_le a 0).trans (bound_ge_half n)
  · exact security n hn a
  · change pairWin (explicitScheme n) a 1 0 ≤ _
    rw [pairWin_swap]
    exact security n hn _
  · exact (pairWin_same_le a 1).trans (bound_ge_half n)

lemma generalWin_le [Nonempty B] [Nonempty C] (hn : 1 ≤ n) (a : GeneralAttack n B C) :
    generalWin (explicitScheme n) a ≤
      1/2 + (1/2) * Real.sqrt ((2 : ℝ)^n / ((4 : ℝ)^n - 1)) := by
  set β := 1/2 + (1/2) * Real.sqrt ((2 : ℝ)^n / ((4 : ℝ)^n - 1))
  unfold generalWin
  calc (∑ u, ∑ v, a.mass u v * pairWin (explicitScheme n) (a.conditional u v) u v)
      ≤ ∑ u, ∑ v, a.mass u v * β := by
        apply Finset.sum_le_sum; intro u _
        apply Finset.sum_le_sum; intro v _
        exact mul_le_mul_of_nonneg_left (pairWin_le hn _ u v) (a.nonneg u v)
    _ = β := by
        simp_rw [← Finset.sum_mul]
        rw [a.normalized, one_mul]

end PauliUnclonable531.Pauli.HeadlineAux

open PauliUnclonable531.Pauli PauliUnclonable531.Pauli.HeadlineAux in
theorem solution :
    ∃ family : (n : ℕ) → Scheme n, family = explicitScheme ∧
      (∀ g : Gate, (gateMatrix g).conjTranspose * gateMatrix g = 1 ∧
        ∀ p : Fin 4, ∃ q : Fin 4, ∃ b : Fin 2,
          gateMatrix g * QMaxCutSDP.Rounding.pauli p * (gateMatrix g).conjTranspose =
            sign b • QMaxCutSDP.Rounding.pauli q) ∧
      ∀ n : ℕ, 1 ≤ n →
        Fintype.card (Key n) = 4^n - 1 ∧
        Function.Injective (@keyEncode n) ∧
        Fintype.card (Fin (n+n)) = 2*n ∧
        Fintype.card (Bits n) = 2^n ∧
        (∀ k, (family n).gen k = (Fintype.card (Key n) : ℝ)⁻¹ ∧ 0 < (family n).gen k) ∧
        (∑ k : Key n, (family n).gen k) = 1 ∧
        (∀ k m, Density ((family n).enc k m)) ∧
        (∀ k, (∀ m, ((family n).dec k m).PosSemidef) ∧ (∑ m, (family n).dec k m) = 1) ∧
        (∀ k m, born ((family n).dec k m) ((family n).enc k m) = 1) ∧
        (∀ k m, operationalEnc k m = (family n).enc k m) ∧
        (∀ k : Key n, (∃ j, pivot k = some j ∧ active k.val j = true ∧
                    ∀ i : Fin n, i < j → active k.val i = false) ∧
          Fintype.card (Tape k) = 2^(n-1) ∧
          fairCount (encProgram k) = n-1 ∧ preparationCount (encProgram k) = n ∧
          gateCount (encProgram k) ≤ 2*n ∧ encBitCost k ≤ 100*(n+1)^2) ∧
        (∀ k (σ : Op (Bits n)), Density σ → ∀ b : Fin 2,
          operationalDec k σ b = born ((family n).dec k b) σ) ∧
        (∀ k : Key n, (decProgram k).length ≤ n ∧ decBitCost k ≤ 100*(n+1)^2) ∧
        (∀ (B C : Type) [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
            [Nonempty B] [Nonempty C] (a : GeneralAttack n B C),
          generalWin (family n) a ≤ 1/2 + (1/2) * Real.sqrt ((2 : ℝ)^n / ((4 : ℝ)^n - 1))) := by
  refine ⟨explicitScheme, rfl, gate_facts, ?_⟩
  intro n hn
  have hcard : (0 : ℝ) < Fintype.card (Key n) := by
    rw [card_key]
    have : 1 < 4 ^ n := Nat.one_lt_pow (by omega) (by norm_num)
    exact_mod_cast Nat.sub_pos_of_lt this
  refine ⟨card_key n, keyEncode_injective n, by simp [two_mul], by simp [Bits],
    fun k => ⟨rfl, inv_pos.mpr hcard⟩, ?_, ciphertext_density, fun k =>
      ⟨decryptEffect_psd k, decryptEffect_sum k⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ∑ _k : Key n, (Fintype.card (Key n) : ℝ)⁻¹ = 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard.ne']
  · intro k m
    change born (decryptEffect k m) (ciphertext k m) = 1
    rw [correctness n hn k m m, if_pos rfl]
  · intro k m
    change operationalEnc k m = ciphertext k m
    rw [encryption_execution n hn k m, preparation n hn k m]
  · intro k
    obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := resource_counts n hn k
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · intro k σ _ b
    exact decryption_execution n k σ b
  · intro k
    obtain ⟨-, -, -, -, -, -, h7, h8⟩ := resource_counts n hn k
    exact ⟨h7, h8⟩
  · intro B C _ _ _ _ _ _ a
    exact generalWin_le hn a
