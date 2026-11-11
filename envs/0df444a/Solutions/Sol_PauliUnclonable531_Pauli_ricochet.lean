-- Prove2me | solution 1 for PauliUnclonable531.Pauli.ricochet
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T10:49:02.470253+00:00
-- url     : https://prove2.me/submissions/d7f2a6b8-df66-467c-8426-89fcf20445f3

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Correlations
import Theorems.Thm_PauliUnclonable531_Pauli_choi_identity

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli.Kit



open PauliUnclonable531.Pauli

/-- The tensor product `⊗ᵢ fᵢ` of single-qubit matrices, on the computational basis. -/
def tens {n : ℕ} (f : Fin n → Op (Fin 2)) : Op (Bits n) := fun x y => ∏ i, f i (x i) (y i)

lemma tens_mul {n : ℕ} (f g : Fin n → Op (Fin 2)) :
    tens f * tens g = tens (fun i => f i * g i) := by
  ext x y
  simp only [tens, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp [Finset.prod_mul_distrib]

lemma tens_one {n : ℕ} : tens (fun _ : Fin n => (1 : Op (Fin 2))) = 1 := by
  ext x y
  simp only [tens, Matrix.one_apply]
  rw [Finset.prod_boole]
  simp [funext_iff]

lemma tens_smul {n : ℕ} (c : Fin n → ℂ) (f : Fin n → Op (Fin 2)) :
    tens (fun i => c i • f i) = (∏ i, c i) • tens f := by
  ext x y
  simp [tens, Finset.prod_mul_distrib]

lemma tens_conjTranspose {n : ℕ} (f : Fin n → Op (Fin 2)) :
    (tens f).conjTranspose = tens (fun i => (f i).conjTranspose) := by
  ext x y
  simp [tens, star_prod]

lemma tens_transpose {n : ℕ} (f : Fin n → Op (Fin 2)) :
    (tens f).transpose = tens (fun i => (f i).transpose) := by
  ext x y
  simp [tens]

lemma tens_trace {n : ℕ} (f : Fin n → Op (Fin 2)) :
    (tens f).trace = ∏ i, (f i).trace := by
  simp only [Matrix.trace, Matrix.diag, tens]
  rw [Fintype.prod_sum]

lemma pauli_eq_tens {n : ℕ} (k : Label n) :
    pauli k = tens (fun j => QMaxCutSDP.Rounding.pauli (localLabel (k.1 j) (k.2 j))) := rfl

lemma sign_add (a b : Fin 2) : sign (a + b) = sign a * sign b := by
  fin_cases a <;> fin_cases b <;> simp [sign]

lemma sign_sum {ι : Type} (s : Finset ι) (f : ι → Fin 2) :
    sign (∑ i ∈ s, f i) = ∏ i ∈ s, sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sign]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sign_add, ih]


lemma qubit_herm (a : Fin 4) :
    (QMaxCutSDP.Rounding.pauli a).conjTranspose = QMaxCutSDP.Rounding.pauli a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [QMaxCutSDP.Rounding.pauli]

lemma pauli_isHermitian {n : ℕ} (k : Label n) : (pauli k).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [pauli_eq_tens, tens_conjTranspose]
  simp only [qubit_herm]

end PauliUnclonable531.Pauli.Kit

namespace PauliUnclonable531.Pauli.Top


open PauliUnclonable531.Pauli

lemma kron_conjTranspose {X Y : Type} (x : Op X) (y : Op Y) :
    (Matrix.kronecker x y).conjTranspose = Matrix.kronecker x.conjTranspose y.conjTranspose :=
  Matrix.conjTranspose_kronecker x y

lemma avg_hermitian {n : ℕ} {X : Type} [Fintype X] (f : Key n → Op X)
    (hf : ∀ k, (f k).IsHermitian) : ((Fintype.card (Key n) : ℂ)⁻¹ • ∑ k, f k).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  simp only [fun k => (hf k).eq]
  congr 1
  simp

variable {n : ℕ} {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]

lemma transpose_pauli_herm (k : Label n) : ((pauli k).transpose).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, (Kit.pauli_isHermitian k).eq]

lemma EB_herm (a : Decoders n B C) : (EB a).IsHermitian := by
  apply avg_hermitian
  intro k
  unfold Matrix.IsHermitian
  rw [kron_conjTranspose, kron_conjTranspose, (transpose_pauli_herm k.val).eq,
    (a.bob_hermitian k).eq, Matrix.conjTranspose_one]

lemma EC_herm (a : Decoders n B C) : (EC a).IsHermitian := by
  apply avg_hermitian
  intro k
  unfold Matrix.IsHermitian
  rw [kron_conjTranspose, kron_conjTranspose, (transpose_pauli_herm k.val).eq,
    (a.charlie_hermitian k).eq, Matrix.conjTranspose_one]

lemma EBC_herm (a : Decoders n B C) : (EBC a).IsHermitian := by
  apply avg_hermitian
  intro k
  unfold Matrix.IsHermitian
  rw [kron_conjTranspose, kron_conjTranspose, (a.bob_hermitian k).eq,
    (a.charlie_hermitian k).eq, Matrix.conjTranspose_one]

lemma D_herm (a : Decoders n B C) : (disagreement a).IsHermitian :=
  Matrix.isHermitian_one.sub (EBC_herm a)

lemma G_herm (a : Decoders n B C) : (gameOperator a).IsHermitian := by
  unfold gameOperator
  have h := ((EB_herm a).add (EC_herm a)).sub (D_herm a)
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, h.eq]
  congr 1
  simp


end PauliUnclonable531.Pauli.Top

namespace PauliUnclonable531.Pauli.Rico

open PauliUnclonable531.Pauli

lemma kron_sub {l m p q : Type} (A : Matrix l m ℂ) (B₁ B₂ : Matrix p q ℂ) :
    Matrix.kronecker A (B₁ - B₂) = Matrix.kronecker A B₁ - Matrix.kronecker A B₂ := by
  ext ⟨_, _⟩ ⟨_, _⟩; simp [mul_sub]

lemma sub_kron {l m p q : Type} (A₁ A₂ : Matrix l m ℂ) (B : Matrix p q ℂ) :
    Matrix.kronecker (A₁ - A₂) B = Matrix.kronecker A₁ B - Matrix.kronecker A₂ B := by
  ext ⟨_, _⟩ ⟨_, _⟩; simp [sub_mul]

lemma kron_add {l m p q : Type} (A : Matrix l m ℂ) (B₁ B₂ : Matrix p q ℂ) :
    Matrix.kronecker A (B₁ + B₂) = Matrix.kronecker A B₁ + Matrix.kronecker A B₂ := by
  ext ⟨_, _⟩ ⟨_, _⟩; simp [mul_add]

lemma add_kron {l m p q : Type} (A₁ A₂ : Matrix l m ℂ) (B : Matrix p q ℂ) :
    Matrix.kronecker (A₁ + A₂) B = Matrix.kronecker A₁ B + Matrix.kronecker A₂ B := by
  ext ⟨_, _⟩ ⟨_, _⟩; simp [add_mul]

lemma smul_kron {l m p q : Type} (c : ℂ) (A : Matrix l m ℂ) (B : Matrix p q ℂ) :
    Matrix.kronecker (c • A) B = c • Matrix.kronecker A B := by
  ext ⟨_, _⟩ ⟨_, _⟩; simp [mul_assoc]

lemma kron_one_one {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] :
    Matrix.kronecker (1 : Op X) (1 : Op Y) = 1 := Matrix.one_kronecker_one

/-- The normalized maximally entangled projector is positive semidefinite. -/
lemma omega_psd (A : Type) [Fintype A] [DecidableEq A] : (omegaDensity A).PosSemidef := by
  let W : Matrix Unit (A × A) ℂ := Matrix.of fun _ i => if i.1 = i.2 then 1 else 0
  have h := (Matrix.posSemidef_conjTranspose_mul_self W).smul
    (show (0 : ℝ) ≤ ((Fintype.card A : ℝ))⁻¹ by positivity)
  convert h using 1
  ext i j
  simp only [omegaDensity, Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, W,
    Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton]
  by_cases hi : i.1 = i.2 <;> by_cases hj : j.1 = j.2 <;> simp [hi, hj, ← Complex.coe_smul]

/-- Complete positivity transfers from `Fin r` references to any finite reference. -/
lemma idTensor_psd {A O : Type} [Fintype A] [DecidableEq A] [Fintype O]
    (Φ : Op A →ₗ[ℂ] Op O) (hΦ : QAlgorithms.Entanglement.IsCompletelyPositive Φ)
    {X : Op (A × A)} (hX : X.PosSemidef) :
    (QAlgorithms.idTensorSuperop (R := A) Φ X).PosSemidef := by
  let e := Fintype.equivFin A
  have h := hΦ (Fintype.card A) (X.submatrix (fun p => (e.symm p.1, p.2))
    (fun p => (e.symm p.1, p.2))) (hX.submatrix _)
  have heq : QAlgorithms.idTensorSuperop (R := A) Φ X =
      (QAlgorithms.idTensorSuperop Φ (X.submatrix (fun p => (e.symm p.1, p.2))
        (fun p => (e.symm p.1, p.2)))).submatrix (fun p => (e p.1, p.2)) (fun p => (e p.1, p.2)) := by
    ext p q
    simp [QAlgorithms.idTensorSuperop, Matrix.submatrix]
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

end PauliUnclonable531.Pauli.Rico

open PauliUnclonable531.Pauli PauliUnclonable531.Pauli.Rico PauliUnclonable531.Pauli.Top in
theorem solution {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    [Nonempty B] [Nonempty C] (n : ℕ) (hn : 1 ≤ n) (a : Attack n B C) :
    ∃ d : Decoders n B C,
      (∀ k, d.bob k = bobEffect a k 0 - bobEffect a k 1) ∧
      (∀ k, d.charlie k = charlieEffect a k 0 - charlieEffect a k 1) ∧
      Density (choi a.split) ∧
      win a = (1 + born (gameOperator d) (choi a.split)) / 2 ∧
      win a ≤ (1 + largestEigenvalue (gameOperator d)) / 2 := by
  classical
  have hb0 : ∀ k, bobEffect a k 0 = a.bobZero k := fun k => rfl
  have hb1 : ∀ k, bobEffect a k 1 = 1 - a.bobZero k := fun k => rfl
  have hc0 : ∀ k, charlieEffect a k 0 = a.charlieZero k := fun k => rfl
  have hc1 : ∀ k, charlieEffect a k 1 = 1 - a.charlieZero k := fun k => rfl
  -- the decoder families
  let d : Decoders n B C :=
    { bob := fun k => a.bobZero k - (1 - a.bobZero k)
      charlie := fun k => a.charlieZero k - (1 - a.charlieZero k)
      bob_hermitian := fun k =>
        (a.bob_pos k).isHermitian.sub (a.bob_complement_pos k).isHermitian
      charlie_hermitian := fun k =>
        (a.charlie_pos k).isHermitian.sub (a.charlie_complement_pos k).isHermitian
      bob_lower := fun k => by
        unfold Below
        have := (a.bob_pos k).smul (show (0 : ℝ) ≤ 2 by norm_num)
        convert this using 1
        rw [two_smul]; abel
      bob_upper := fun k => by
        unfold Below
        have := (a.bob_complement_pos k).smul (show (0 : ℝ) ≤ 2 by norm_num)
        convert this using 1
        rw [two_smul]; abel
      charlie_lower := fun k => by
        unfold Below
        have := (a.charlie_pos k).smul (show (0 : ℝ) ≤ 2 by norm_num)
        convert this using 1
        rw [two_smul]; abel
      charlie_upper := fun k => by
        unfold Below
        have := (a.charlie_complement_pos k).smul (show (0 : ℝ) ≤ 2 by norm_num)
        convert this using 1
        rw [two_smul]; abel }
  set J := choi a.split with hJ
  have hdim : (Fintype.card (Bits n) : ℂ) = (2 : ℂ) ^ n := by simp [Bits]
  have hdne : (Fintype.card (Bits n) : ℂ) ≠ 0 := by rw [hdim]; exact pow_ne_zero _ two_ne_zero
  -- the Choi state is a density operator
  have hJtr : J.trace = 1 := by
    have h := choi_identity a.split a.channel (1 : Op (Bits n)) (1 : Op (B × C))
    rw [Matrix.transpose_one, kron_one_one, Matrix.one_mul, Matrix.one_mul, a.channel.2,
      Matrix.trace_one] at h
    rw [← h, inv_mul_cancel₀ hdne]
  have hJpsd : J.PosSemidef := idTensor_psd a.split a.channel.1 (omega_psd _)
  -- Born probabilities through the Choi state
  have hborn : ∀ (k : Key n) (m : Fin 2) (X : Op (B × C)),
      (X * a.split (ciphertext k m)).trace =
        (Matrix.kronecker (1 + sign m • (pauli k.val).transpose) X * J).trace := by
    intro k m X
    have h := choi_identity a.split a.channel (ciphertext k m) X
    have hT : (ciphertext k m).transpose =
        (Fintype.card (Bits n) : ℂ)⁻¹ • (1 + sign m • (pauli k.val).transpose) := by
      rw [ciphertext, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_smul,
        Matrix.transpose_one, hdim]
    rw [hT, smul_kron, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at h
    exact mul_left_cancel₀ (inv_ne_zero hdne) h
  -- the per-key operator identity
  set Qt : Key n → Op (Bits n) := fun k => (pauli k.val).transpose
  have hkey : ∀ k : Key n, (∑ b : Fin 2, Matrix.kronecker (1 + sign b • Qt k)
      (Matrix.kronecker (bobEffect a k b) (charlieEffect a k b))) =
      (1/2 : ℂ) • (Matrix.kronecker (1 : Op (Bits n)) (Matrix.kronecker (1 : Op B) (1 : Op C)) +
        Matrix.kronecker 1 (Matrix.kronecker (d.bob k) (d.charlie k)) +
        Matrix.kronecker (Qt k) (Matrix.kronecker (d.bob k) 1) +
        Matrix.kronecker (Qt k) (Matrix.kronecker 1 (d.charlie k))) := by
    intro k
    rw [Fin.sum_univ_two, hb0, hb1, hc0, hc1]
    simp only [d, sign, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul,
      kron_sub, sub_kron, kron_add, add_kron, smul_kron, ← sub_eq_add_neg]
    module
  -- assemble the averaged identity
  have hK : (Fintype.card (Key n) : ℂ) ≠ 0 := by
    have : 0 < Fintype.card (Key n) := Fintype.card_pos_iff.mpr ⟨⟨(fun _ => 1, 0), by
      intro h; have := congrFun (congrArg Prod.fst h) ⟨0, hn⟩; simp at this⟩⟩
    exact_mod_cast this.ne'
  have havg1 : (Fintype.card (Key n) : ℂ)⁻¹ • ∑ _k : Key n,
      Matrix.kronecker (1 : Op (Bits n)) (Matrix.kronecker (1 : Op B) (1 : Op C)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ hK, one_smul, kron_one_one, kron_one_one]
  set M : Key n → Op (Bits n × (B × C)) := fun k =>
    (1/2 : ℂ) • (Matrix.kronecker (1 : Op (Bits n)) (Matrix.kronecker (1 : Op B) (1 : Op C)) +
      Matrix.kronecker 1 (Matrix.kronecker (d.bob k) (d.charlie k)) +
      Matrix.kronecker (Qt k) (Matrix.kronecker (d.bob k) 1) +
      Matrix.kronecker (Qt k) (Matrix.kronecker 1 (d.charlie k))) with hMdef
  have hsumk : ∀ k : Key n, (∑ b : Fin 2, (Matrix.kronecker (bobEffect a k b) (charlieEffect a k b) *
      a.split ((explicitScheme n).enc k (if b = 0 then 0 else 1))).trace) = (M k * J).trace := by
    intro k
    simp only [hMdef]
    rw [← hkey k, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hm : (if b = 0 then (0 : Fin 2) else 1) = b := by fin_cases b <;> rfl
    rw [hm]
    exact hborn k b _
  have hMavg : (Fintype.card (Key n) : ℂ)⁻¹ • ∑ k, M k =
      (1/2 : ℂ) • (1 + EBC d + EB d + EC d) := by
    simp only [hMdef, ← Finset.smul_sum, smul_comm _ (1/2 : ℂ), Finset.sum_add_distrib, smul_add]
    rw [havg1]
    rfl
  have hwin : win a = (∑ k : Key n, (((explicitScheme n).gen k : ℝ) : ℂ) * ((1/2 : ℂ) *
      ∑ b : Fin 2, (Matrix.kronecker (bobEffect a k b) (charlieEffect a k b) *
        a.split ((explicitScheme n).enc k (if b = 0 then 0 else 1))).trace)).re := by
    unfold win pairWin born
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.re_ofReal_mul, show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul,
      Complex.re_sum]
  have hgen : ∀ k : Key n, (((explicitScheme n).gen k : ℝ) : ℂ) =
      (Fintype.card (Key n) : ℂ)⁻¹ := by intro k; simp [explicitScheme, keyMass]
  have hC : (∑ k : Key n, (((explicitScheme n).gen k : ℝ) : ℂ) * ((1/2 : ℂ) *
      ∑ b : Fin 2, (Matrix.kronecker (bobEffect a k b) (charlieEffect a k b) *
        a.split ((explicitScheme n).enc k (if b = 0 then 0 else 1))).trace)) =
      (1 + (gameOperator d * J).trace) / 2 := by
    simp only [hgen, hsumk]
    have : (∑ k : Key n, (Fintype.card (Key n) : ℂ)⁻¹ * ((1/2 : ℂ) * (M k * J).trace)) =
        (1/2 : ℂ) * (((Fintype.card (Key n) : ℂ)⁻¹ • ∑ k, M k) * J).trace := by
      rw [Matrix.smul_mul, Matrix.trace_smul, Finset.sum_mul, Matrix.trace_sum, smul_eq_mul,
        Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this, hMavg]
    unfold gameOperator disagreement
    simp only [Matrix.smul_mul, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_smul,
      Matrix.trace_add, Matrix.trace_sub, hJtr, smul_eq_mul]
    ring
  have hwin' : win a = (1 + born (gameOperator d) J) / 2 := by
    rw [hwin, hC]
    unfold born
    simp [Complex.add_re, Complex.div_re]
  refine ⟨d, fun k => by rw [hb0, hb1], fun k => by rw [hc0, hc1], ⟨hJpsd, hJtr⟩, hwin', ?_⟩
  -- the largest-eigenvalue bound
  have hG := G_herm d
  set lam := largestEigenvalue (gameOperator d) with hlam
  have hlamval : lam = Finset.univ.sup' Finset.univ_nonempty hG.eigenvalues := by
    rw [hlam, largestEigenvalue, dif_pos hG]
  have hle : (lam • (1 : Op (Bits n × (B × C))) - gameOperator d).PosSemidef := by
    open scoped MatrixOrder in
    have h := le_algebraMap_of_spectrum_le (R := ℝ) (a := gameOperator d) (r := lam)
      (fun x hx => by
        rw [hG.spectrum_real_eq_range_eigenvalues] at hx
        obtain ⟨i, rfl⟩ := hx
        rw [hlamval]
        exact Finset.le_sup' _ (Finset.mem_univ i)) hG.isSelfAdjoint
    open scoped MatrixOrder in
    have h2 := Matrix.le_iff.mp h
    rwa [Algebra.algebraMap_eq_smul_one] at h2
  have hpos := born_nonneg hle hJpsd
  have hsplit : born (lam • (1 : Op (Bits n × (B × C))) - gameOperator d) J =
      lam - born (gameOperator d) J := by
    unfold born
    rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, hJtr]
    simp
  rw [hwin']
  linarith
