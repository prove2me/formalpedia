-- Prove2me | solution 1 for PauliUnclonable531.Pauli.correlation_product
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T10:28:43.179047+00:00
-- url     : https://prove2.me/submissions/1a818e30-ac8a-45e8-b7ba-e11d187f521a

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Correlations
import Definitions.Def_PauliUnclonable531_Pauli_Symplectic
import Theorems.Thm_PauliUnclonable531_Pauli_character_norm
import Theorems.Thm_PauliUnclonable531_Pauli_pauli_commutation
import Theorems.Thm_PauliUnclonable531_Pauli_pauli_bridges

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

namespace PauliUnclonable531.Pauli.Corr

open PauliUnclonable531.Pauli
open scoped MatrixOrder

/-! ## Kronecker algebra -/

lemma kron_mul {a b c d e f : Type} [Fintype b] [Fintype e] (A : Matrix a b ℂ) (A' : Matrix b c ℂ)
    (Bm : Matrix d e ℂ) (B' : Matrix e f ℂ) :
    Matrix.kronecker A Bm * Matrix.kronecker A' B' = Matrix.kronecker (A * A') (Bm * B') :=
  (Matrix.mul_kronecker_mul A A' Bm B').symm

lemma kron_conjTranspose {X Y : Type} (x : Op X) (y : Op Y) :
    (Matrix.kronecker x y).conjTranspose = Matrix.kronecker x.conjTranspose y.conjTranspose :=
  Matrix.conjTranspose_kronecker x y

lemma kron_sub {l m p q : Type} (A : Matrix l m ℂ) (B₁ B₂ : Matrix p q ℂ) :
    Matrix.kronecker A (B₁ - B₂) = Matrix.kronecker A B₁ - Matrix.kronecker A B₂ := by
  ext ⟨_, _⟩ ⟨_, _⟩; simp [mul_sub]

lemma sub_kron {l m p q : Type} (A₁ A₂ : Matrix l m ℂ) (B : Matrix p q ℂ) :
    Matrix.kronecker (A₁ - A₂) B = Matrix.kronecker A₁ B - Matrix.kronecker A₂ B := by
  ext ⟨_, _⟩ ⟨_, _⟩; simp [sub_mul]

lemma add_kron {l m p q : Type} (A₁ A₂ : Matrix l m ℂ) (B : Matrix p q ℂ) :
    Matrix.kronecker (A₁ + A₂) B = Matrix.kronecker A₁ B + Matrix.kronecker A₂ B := by
  ext ⟨_, _⟩ ⟨_, _⟩; simp [add_mul]

lemma smul_kron {l m p q : Type} (c : ℂ) (A : Matrix l m ℂ) (B : Matrix p q ℂ) :
    Matrix.kronecker (c • A) B = c • Matrix.kronecker A B := by
  ext ⟨_, _⟩ ⟨_, _⟩; simp [mul_assoc]

lemma kron_one_one {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] :
    Matrix.kronecker (1 : Op X) (1 : Op Y) = 1 := Matrix.one_kronecker_one

lemma psd_kron {X Y : Type} [Fintype X] [Fintype Y] {x : Op X} {y : Op Y}
    (hx : x.PosSemidef) (hy : y.PosSemidef) : (Matrix.kronecker x y).PosSemidef :=
  hx.kronecker hy

/-! ## Norm bounds from Loewner bounds -/

variable {A : Type} [Fintype A] [DecidableEq A]

lemma one_sub_sq_psd (X : Op A) (hX : X.IsHermitian) (h1 : (1 - X).PosSemidef)
    (h2 : (1 + X).PosSemidef) : (1 - X * X).PosSemidef := by
  have ha := h2.conjTranspose_mul_mul_same (1 - X)
  have hb := h1.conjTranspose_mul_mul_same (1 + X)
  have hsum := (ha.add hb).smul (show (0:ℝ) ≤ 1/2 by norm_num)
  have hc1 : (1 - X).conjTranspose = 1 - X := by simp [hX.eq]
  have hc2 : (1 + X).conjTranspose = 1 + X := by simp [hX.eq]
  rw [hc1, hc2] at hsum
  convert hsum using 1
  simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one]
  module

lemma norm_one_le : ‖(1 : Op A)‖ ≤ 1 := by
  rcases isEmpty_or_nonempty A with hA | hA
  · simp [Subsingleton.elim (1 : Op A) 0]
  · simp

lemma norm_le_one_of_contraction (X : Op A) (hX : X.IsHermitian) (h1 : (1 - X).PosSemidef)
    (h2 : (1 + X).PosSemidef) : ‖X‖ ≤ 1 := by
  have hsq : ‖X * X‖ ≤ ‖(1 : Op A)‖ := by
    apply CStarAlgebra.norm_le_norm_of_nonneg_of_le
    · have := Matrix.posSemidef_conjTranspose_mul_self X
      rw [hX.eq] at this
      exact this.nonneg
    · rw [Matrix.le_iff]; exact one_sub_sq_psd X hX h1 h2
  have : ‖X‖ * ‖X‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self, Matrix.star_eq_conjTranspose, hX.eq]
    exact hsq.trans norm_one_le
  nlinarith [norm_nonneg X]

lemma norm_le_of_two_sided (X : Op A) (hX : X.IsHermitian) {c : ℝ} (hc : 0 < c)
    (h1 : (c • 1 - X).PosSemidef) (h2 : (c • 1 + X).PosSemidef) : ‖X‖ ≤ c := by
  have hY : (c⁻¹ • X).IsHermitian := by
    unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_smul, hX.eq]; simp
  have e1 : 1 - c⁻¹ • X = c⁻¹ • (c • 1 - X) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  have e2 : 1 + c⁻¹ • X = c⁻¹ • (c • 1 + X) := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  have := norm_le_one_of_contraction (c⁻¹ • X) hY
    (by rw [e1]; exact h1.smul (inv_nonneg.mpr hc.le))
    (by rw [e2]; exact h2.smul (inv_nonneg.mpr hc.le))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)] at this
  rwa [inv_mul_le_iff₀ hc, mul_one] at this

/-- A positive semidefinite operator below `c • 1` has norm at most `c`. -/
lemma norm_le_of_psd_le (M : Op A) (hM : M.PosSemidef) {c : ℝ} (hc : 0 ≤ c)
    (h : (c • 1 - M).PosSemidef) : ‖M‖ ≤ c := by
  have := CStarAlgebra.norm_le_norm_of_nonneg_of_le hM.nonneg (Matrix.le_iff.mpr h)
  refine this.trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  exact mul_le_of_le_one_right hc norm_one_le

/-! ## Block rows and columns -/

variable {κ : Type} [Fintype κ] [DecidableEq κ]

def blockRow (V : κ → Op A) : Matrix A (κ × A) ℂ := fun i p => V p.1 i p.2
def blockCol (U : κ → Op A) : Matrix (κ × A) A ℂ := fun p j => U p.1 p.2 j

lemma blockRow_mul_conj (V : κ → Op A) :
    blockRow V * (blockRow V).conjTranspose = ∑ φ, V φ * (V φ).conjTranspose := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, blockRow, Matrix.sum_apply,
    Fintype.sum_prod_type]

lemma blockCol_conj_mul (U : κ → Op A) :
    (blockCol U).conjTranspose * blockCol U = ∑ θ, (U θ).conjTranspose * U θ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, blockCol, Matrix.sum_apply,
    Fintype.sum_prod_type]

lemma signed_sum_factor (Γ : Op κ) (U V : κ → Op A)
    (hcomm : ∀ θ φ, U θ * V φ = Γ φ θ • (V φ * U θ)) :
    (∑ θ, ∑ φ, U θ * V φ) = blockRow V * Matrix.kronecker Γ (1 : Op A) * blockCol U := by
  calc (∑ θ, ∑ φ, U θ * V φ) = ∑ θ, ∑ φ, Γ φ θ • (V φ * U θ) := by
        simp only [hcomm]
    _ = ∑ φ, ∑ θ, Γ φ θ • (V φ * U θ) := Finset.sum_comm
    _ = blockRow V * Matrix.kronecker Γ (1 : Op A) * blockCol U := by
      ext i j
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply, blockRow, blockCol,
        Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
        smul_eq_mul]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun φ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun θ _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      ring

lemma blockRow_sq_le (V : κ → Op A) {c : ℝ} (hc : 0 ≤ c)
    (h : (c • 1 - ∑ φ, V φ * (V φ).conjTranspose).PosSemidef) :
    ‖blockRow V‖ * ‖blockRow V‖ ≤ c := by
  rw [← Matrix.l2_opNorm_conjTranspose, ← Matrix.l2_opNorm_conjTranspose_mul_self,
    Matrix.conjTranspose_conjTranspose, blockRow_mul_conj]
  apply norm_le_of_psd_le _ _ hc h
  exact Matrix.posSemidef_sum _ fun φ _ => by
    simpa using Matrix.posSemidef_conjTranspose_mul_self (V φ).conjTranspose

lemma blockCol_sq_le (U : κ → Op A) {c : ℝ} (hc : 0 ≤ c)
    (h : (c • 1 - ∑ θ, (U θ).conjTranspose * U θ).PosSemidef) :
    ‖blockCol U‖ * ‖blockCol U‖ ≤ c := by
  rw [← Matrix.l2_opNorm_conjTranspose_mul_self, blockCol_conj_mul]
  apply norm_le_of_psd_le _ _ hc h
  exact Matrix.posSemidef_sum _ fun θ _ => Matrix.posSemidef_conjTranspose_mul_self (U θ)

end PauliUnclonable531.Pauli.Corr

namespace PauliUnclonable531.Pauli.Corr

open PauliUnclonable531.Pauli
open scoped MatrixOrder

/-! ## The Pauli game -/

lemma sign_real (c : Fin 2) : star (sign c) = sign c := by
  fin_cases c <;> simp [sign]

lemma symplectic_comm {n : ℕ} (k l : Label n) : symplectic k l = symplectic l k := by
  unfold symplectic
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [add_comm, mul_comm (l.2 j), mul_comm (l.1 j)]

lemma character_herm (n : ℕ) : (character n).conjTranspose = character n := by
  ext k l
  simp only [Matrix.conjTranspose_apply, character]
  rw [symplectic_comm, sign_real]

lemma transpose_pauli_herm {n : ℕ} (k : Label n) : ((pauli k).transpose).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, (Kit.pauli_isHermitian k).eq]

lemma card_key_real {n : ℕ} (hn : 1 ≤ n) : (Fintype.card (Key n) : ℝ) = (4 : ℝ) ^ n - 1 := by
  have hc : Fintype.card (Key n) = 4 ^ n - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_prod]
    simp [Bits, ← mul_pow]
  have h1 : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
  rw [hc, Nat.cast_sub h1]
  push_cast; ring

end PauliUnclonable531.Pauli.Corr

open scoped MatrixOrder

open PauliUnclonable531.Pauli PauliUnclonable531.Pauli.Corr in
theorem solution {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    [Nonempty B] [Nonempty C] (n : ℕ) (hn : 1 ≤ n) (a : Decoders n B C) :
    PauliUnclonable531.Pauli.spectralNorm (EB a * EC a) ≤ gamma n := by
  classical
  set K : ℝ := (Fintype.card (Key n) : ℝ) with hK
  have hKval : K = (4 : ℝ) ^ n - 1 := card_key_real hn
  have hKpos : 0 < K := by
    rw [hKval]
    have : (1 : ℝ) < 4 ^ n := one_lt_pow₀ (by norm_num) (by omega)
    linarith
  -- the factors
  set U : Key n → Op (Bits n × (B × C)) := fun k =>
    Matrix.kronecker (pauli k.val).transpose (Matrix.kronecker (a.bob k) (1 : Op C)) with hU
  set V : Key n → Op (Bits n × (B × C)) := fun k =>
    Matrix.kronecker (pauli k.val).transpose (Matrix.kronecker (1 : Op B) (a.charlie k)) with hV
  set Γ : Op (Key n) := (character n).submatrix Subtype.val Subtype.val with hΓ
  -- commutation
  have hcomm : ∀ θ φ, U θ * V φ = Γ φ θ • (V φ * U θ) := by
    intro θ φ
    simp only [hU, hV, hΓ, Matrix.submatrix_apply, character, kron_mul, Matrix.mul_one,
      Matrix.one_mul]
    rw [(pauli_commutation n θ.val φ.val).2, smul_kron, symplectic_comm]
  have hprod : EB a * EC a = ((K⁻¹ * K⁻¹ : ℝ) : ℂ) •
      (blockRow V * Matrix.kronecker Γ (1 : Op (Bits n × (B × C))) * blockCol U) := by
    rw [← signed_sum_factor Γ U V hcomm]
    unfold EB EC
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Finset.sum_mul]
    simp only [Finset.mul_sum]
    congr 1
    push_cast; rfl
  -- norm of the middle factor
  have hΓnorm : ‖Matrix.kronecker Γ (1 : Op (Bits n × (B × C)))‖ ≤ (2 : ℝ) ^ n := by
    have hchar := character_norm n
    unfold PauliUnclonable531.Pauli.spectralNorm at hchar
    have hsa : IsSelfAdjoint (character n) := by
      rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, character_herm]
    have hup := Matrix.le_iff.mp hsa.le_algebraMap_norm_self
    have hlo := Matrix.le_iff.mp hsa.neg_algebraMap_norm_le_self
    rw [hchar, Algebra.algebraMap_eq_smul_one] at hup hlo
    have hup' := (hup.submatrix (Subtype.val : Key n → Label n))
    have hlo' := (hlo.submatrix (Subtype.val : Key n → Label n))
    have e1 : ((2 : ℝ) ^ n • (1 : Op (Label n)) - character n).submatrix
        (Subtype.val : Key n → Label n) Subtype.val = (2 : ℝ) ^ n • (1 : Op (Key n)) - Γ := by
      ext i j; simp [hΓ, Matrix.one_apply, Subtype.ext_iff]
    have e2 : (character n - -((2 : ℝ) ^ n • (1 : Op (Label n)))).submatrix
        (Subtype.val : Key n → Label n) Subtype.val = (2 : ℝ) ^ n • (1 : Op (Key n)) + Γ := by
      ext i j; simp [hΓ, Matrix.one_apply, Subtype.ext_iff]; ring
    rw [e1] at hup'
    rw [e2] at hlo'
    have hΓH : Γ.IsHermitian := by
      unfold Matrix.IsHermitian
      rw [hΓ, Matrix.conjTranspose_submatrix, character_herm]
    apply norm_le_of_two_sided _ _ (by positivity)
    · have := psd_kron hup' (Matrix.PosSemidef.one (n := Bits n × (B × C)))
      rwa [sub_kron, ← Complex.coe_smul, smul_kron, kron_one_one, Complex.coe_smul] at this
    · have := psd_kron hlo' (Matrix.PosSemidef.one (n := Bits n × (B × C)))
      rwa [add_kron, ← Complex.coe_smul, smul_kron, kron_one_one, Complex.coe_smul] at this
    · unfold Matrix.IsHermitian
      rw [kron_conjTranspose, hΓH.eq, Matrix.conjTranspose_one]
  -- norms of the outer factors
  have hBB : ∀ k, (1 - a.bob k * a.bob k).PosSemidef := fun k =>
    one_sub_sq_psd _ (a.bob_hermitian k) (a.bob_upper k)
      (by have := a.bob_lower k; unfold Below at this; rwa [sub_neg_eq_add, add_comm] at this)
  have hCC : ∀ k, (1 - a.charlie k * a.charlie k).PosSemidef := fun k =>
    one_sub_sq_psd _ (a.charlie_hermitian k) (a.charlie_upper k)
      (by have := a.charlie_lower k; unfold Below at this; rwa [sub_neg_eq_add, add_comm] at this)
  have hQQ : ∀ k : Key n, (pauli k.val).transpose * (pauli k.val).transpose = 1 :=
    fun k => (pauli_bridges n k.val).2.1
  have hK1 : K • (1 : Op (Bits n × (B × C))) = ∑ _φ : Key n, (1 : Op (Bits n × (B × C))) := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ]
  have hR : ‖blockRow V‖ * ‖blockRow V‖ ≤ K := by
    apply blockRow_sq_le V hKpos.le
    have : K • (1 : Op (Bits n × (B × C))) - ∑ φ, V φ * (V φ).conjTranspose =
        ∑ φ, Matrix.kronecker (1 : Op (Bits n))
          (Matrix.kronecker (1 : Op B) (1 - a.charlie φ * a.charlie φ)) := by
      rw [hK1, ← Finset.sum_sub_distrib]
      · refine Finset.sum_congr rfl fun φ _ => ?_
        simp only [hV, kron_conjTranspose, (transpose_pauli_herm φ.val).eq, Matrix.conjTranspose_one,
          (a.charlie_hermitian φ).eq, kron_mul, hQQ, Matrix.mul_one, kron_sub, sub_kron,
          kron_one_one]
    rw [this]
    exact Matrix.posSemidef_sum _ fun φ _ =>
      psd_kron Matrix.PosSemidef.one (psd_kron Matrix.PosSemidef.one (hCC φ))
  have hC : ‖blockCol U‖ * ‖blockCol U‖ ≤ K := by
    apply blockCol_sq_le U hKpos.le
    have : K • (1 : Op (Bits n × (B × C))) - ∑ θ, (U θ).conjTranspose * U θ =
        ∑ θ, Matrix.kronecker (1 : Op (Bits n))
          (Matrix.kronecker (1 - a.bob θ * a.bob θ) (1 : Op C)) := by
      rw [hK1, ← Finset.sum_sub_distrib]
      · refine Finset.sum_congr rfl fun θ _ => ?_
        simp only [hU, kron_conjTranspose, (transpose_pauli_herm θ.val).eq, Matrix.conjTranspose_one,
          (a.bob_hermitian θ).eq, kron_mul, hQQ, Matrix.mul_one, kron_sub, sub_kron,
          kron_one_one]
    rw [this]
    exact Matrix.posSemidef_sum _ fun θ _ =>
      psd_kron Matrix.PosSemidef.one (psd_kron (hBB θ) Matrix.PosSemidef.one)
  have hRC : ‖blockRow V‖ * ‖blockCol U‖ ≤ K := by
    nlinarith [norm_nonneg (blockRow V), norm_nonneg (blockCol U),
      sq_nonneg (‖blockRow V‖ - ‖blockCol U‖)]
  -- assemble
  unfold PauliUnclonable531.Pauli.spectralNorm gamma
  rw [hprod, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  set M := Matrix.kronecker Γ (1 : Op (Bits n × (B × C)))
  have h1 : ‖blockRow V * M * blockCol U‖ ≤ ‖blockRow V * M‖ * ‖blockCol U‖ :=
    Matrix.l2_opNorm_mul (blockRow V * M) (blockCol U)
  have h2 : ‖blockRow V * M‖ ≤ ‖blockRow V‖ * ‖M‖ := Matrix.l2_opNorm_mul (blockRow V) M
  have h3 : ‖blockRow V * M * blockCol U‖ ≤ (2 : ℝ) ^ n * K := by
    calc ‖blockRow V * M * blockCol U‖ ≤ ‖blockRow V * M‖ * ‖blockCol U‖ := h1
      _ ≤ ‖blockRow V‖ * ‖M‖ * ‖blockCol U‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = ‖M‖ * (‖blockRow V‖ * ‖blockCol U‖) := by ring
      _ ≤ (2 : ℝ) ^ n * K :=
          mul_le_mul hΓnorm hRC (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (pow_nonneg (by norm_num) n)
  calc K⁻¹ * K⁻¹ * ‖blockRow V * M * blockCol U‖ ≤ K⁻¹ * K⁻¹ * ((2 : ℝ) ^ n * K) := by
        exact mul_le_mul_of_nonneg_left h3 (mul_nonneg (inv_nonneg.mpr hKpos.le) (inv_nonneg.mpr hKpos.le))
    _ = (2 : ℝ) ^ n / ((4 : ℝ) ^ n - 1) := by
        rw [← hKval]; field_simp
