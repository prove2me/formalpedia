-- Prove2me | solution 1 for PauliUnclonable531.Pauli.difference_order
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T10:05:36.161526+00:00
-- url     : https://prove2.me/submissions/c49625a9-c102-449a-9d38-6e28d1df865c

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Correlations
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

namespace PauliUnclonable531.Pauli.GameKit


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

lemma kron_one_one {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] :
    Matrix.kronecker (1 : Op X) (1 : Op Y) = 1 := Matrix.one_kronecker_one

lemma psd_kron {X Y : Type} [Fintype X] [Fintype Y] {x : Op X} {y : Op Y}
    (hx : x.PosSemidef) (hy : y.PosSemidef) : (Matrix.kronecker x y).PosSemidef :=
  hx.kronecker hy

/-- For Hermitian contractions `B`, `C`, the operator `1 - B ⊗ C` is positive semidefinite. -/
lemma one_sub_kron_psd {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (B : Op X) (C : Op Y) (hB1 : (1 - B).PosSemidef) (hB2 : (1 + B).PosSemidef)
    (hC1 : (1 - C).PosSemidef) (hC2 : (1 + C).PosSemidef) :
    (1 - Matrix.kronecker B C).PosSemidef := by
  have h := ((psd_kron hB1 hC2).add (psd_kron hB2 hC1)).smul (show (0 : ℝ) ≤ 1/2 by norm_num)
  convert h using 1
  simp only [kron_sub, sub_kron, kron_add, add_kron, kron_one_one]
  module

variable {n : ℕ} {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]

lemma bob_add_one (a : Decoders n B C) (k : Key n) : (1 + a.bob k).PosSemidef := by
  have := a.bob_lower k
  unfold Below at this
  rwa [sub_neg_eq_add, add_comm] at this

lemma charlie_add_one (a : Decoders n B C) (k : Key n) : (1 + a.charlie k).PosSemidef := by
  have := a.charlie_lower k
  unfold Below at this
  rwa [sub_neg_eq_add, add_comm] at this

lemma card_key_ne_zero (hn : 1 ≤ n) : (Fintype.card (Key n) : ℂ) ≠ 0 := by
  have : 0 < Fintype.card (Key n) := by
    rw [Fintype.card_pos_iff]
    refine ⟨⟨(fun _ => 1, 0), ?_⟩⟩
    intro h
    have := congrFun (congrArg Prod.fst h) ⟨0, hn⟩
    simp at this
  exact_mod_cast this.ne'

lemma avg_const (hn : 1 ≤ n) {X : Type} [Fintype X] (M : Op X) :
    (Fintype.card (Key n) : ℂ)⁻¹ • ∑ _k : Key n, M = M := by
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (card_key_ne_zero hn), one_smul]

lemma disagreement_eq (hn : 1 ≤ n) (a : Decoders n B C) :
    disagreement a = (Fintype.card (Key n) : ℂ)⁻¹ • ∑ k : Key n,
      Matrix.kronecker (1 : Op (Bits n)) (1 - Matrix.kronecker (a.bob k) (a.charlie k)) := by
  unfold disagreement EBC
  conv_lhs => rw [← avg_const hn (1 : Op (Bits n × (B × C)))]
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [kron_sub, kron_one_one]

lemma disagreement_psd (hn : 1 ≤ n) (a : Decoders n B C) : (disagreement a).PosSemidef := by
  rw [disagreement_eq hn]
  apply Matrix.PosSemidef.smul _ (by
    rw [show ((Fintype.card (Key n) : ℂ))⁻¹ = (((Fintype.card (Key n) : ℝ))⁻¹ : ℝ) by push_cast; rfl]
    exact_mod_cast (inv_nonneg.mpr (Nat.cast_nonneg _)))
  apply Matrix.posSemidef_sum
  intro k _
  exact psd_kron Matrix.PosSemidef.one (one_sub_kron_psd _ _ (a.bob_upper k) (bob_add_one a k)
    (a.charlie_upper k) (charlie_add_one a k))

lemma real_smul_eq (t : ℝ) {X : Type} [Fintype X] (M : Op X) :
    (2 * (t : ℂ)) • M = (2 * t : ℝ) • M := by
  rw [← Complex.coe_smul]; push_cast; rfl


/-- `1 + Q` is positive semidefinite for a Hermitian involution `Q`. -/
lemma one_add_psd {X : Type} [Fintype X] [DecidableEq X] (Q : Op X) (hQ : Q.IsHermitian)
    (hQQ : Q * Q = 1) : (1 + Q).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (1 + Q)
  have heq : (1 + Q).conjTranspose * (1 + Q) = (2 : ℝ) • (1 + Q) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hQ.eq]
    simp only [add_mul, mul_add, hQQ, one_mul, mul_one, two_smul]
    abel
  rw [heq] at h
  have := h.smul (show (0 : ℝ) ≤ (2 : ℝ)⁻¹ by norm_num)
  rwa [smul_smul, inv_mul_cancel₀ (by norm_num), one_smul] at this

lemma transposePauli_facts {n : ℕ} (k : Label n) :
    (1 + (pauli k).transpose).PosSemidef ∧ (1 - (pauli k).transpose).PosSemidef := by
  have hH : ((pauli k).transpose).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, (Kit.pauli_isHermitian k).eq]
  have hQQ := (pauli_bridges n k).2.1
  refine ⟨one_add_psd _ hH hQQ, ?_⟩
  have := one_add_psd (-(pauli k).transpose) hH.neg (by rw [neg_mul_neg, hQQ])
  rwa [← sub_eq_add_neg] at this

lemma avg_psd {X : Type} [Fintype X] (f : Key n → Op X) (hf : ∀ k, (f k).PosSemidef) :
    ((Fintype.card (Key n) : ℂ)⁻¹ • ∑ k, f k).PosSemidef := by
  apply Matrix.PosSemidef.smul _ (by
    rw [show ((Fintype.card (Key n) : ℂ))⁻¹ = (((Fintype.card (Key n) : ℝ))⁻¹ : ℝ) by push_cast; rfl]
    exact_mod_cast (inv_nonneg.mpr (Nat.cast_nonneg _)))
  exact Matrix.posSemidef_sum _ fun k _ => hf k

end PauliUnclonable531.Pauli.GameKit

open PauliUnclonable531.Pauli PauliUnclonable531.Pauli.GameKit in
theorem solution {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    [Nonempty B] [Nonempty C] (n : ℕ) (hn : 1 ≤ n) (a : Decoders n B C) :
    Below (-disagreement a) (EB a - EC a) ∧ Below (EB a - EC a) (disagreement a) := by
  unfold Below
  rw [disagreement_eq hn]
  unfold EB EC
  constructor
  · rw [sub_neg_eq_add, ← smul_sub, ← smul_add, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply avg_psd
    intro k
    obtain ⟨hQp, hQm⟩ := transposePauli_facts k.val
    have h := ((psd_kron hQp (psd_kron (bob_add_one a k) (a.charlie_upper k))).add
      (psd_kron hQm (psd_kron (a.bob_upper k) (charlie_add_one a k)))).smul
        (show (0 : ℝ) ≤ 1/2 by norm_num)
    convert h using 1
    simp only [kron_sub, sub_kron, kron_add, add_kron, kron_one_one]
    module
  · rw [← smul_sub, ← smul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply avg_psd
    intro k
    obtain ⟨hQp, hQm⟩ := transposePauli_facts k.val
    have h := ((psd_kron hQp (psd_kron (a.bob_upper k) (charlie_add_one a k))).add
      (psd_kron hQm (psd_kron (bob_add_one a k) (a.charlie_upper k)))).smul
        (show (0 : ℝ) ≤ 1/2 by norm_num)
    convert h using 1
    simp only [kron_sub, sub_kron, kron_add, add_kron, kron_one_one]
    module
