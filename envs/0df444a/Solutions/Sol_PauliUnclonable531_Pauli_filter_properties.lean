-- Prove2me | solution 1 for PauliUnclonable531.Pauli.filter_properties
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T10:02:42.882665+00:00
-- url     : https://prove2.me/submissions/e763d5e8-0120-445a-b868-edf85bf8f6d8

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Correlations

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

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

end PauliUnclonable531.Pauli.GameKit

open PauliUnclonable531.Pauli PauliUnclonable531.Pauli.GameKit in
theorem solution {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    [Nonempty B] [Nonempty C] (n : ℕ) (hn : 1 ≤ n) (a : Decoders n B C) (t : ℝ) (ht : 0 < t) :
    ((2 * (t : ℂ)) • (1 : Op (Bits n × (B × C))) + disagreement a).PosDef ∧
    (filterOperator a t).PosDef ∧ Below (filterOperator a t) 1 ∧
    (((2 * (t : ℂ)) • 1 + disagreement a) * filterOperator a t = (2 * (t : ℂ)) • 1) ∧
    (filterOperator a t * ((2 * (t : ℂ)) • 1 + disagreement a) = (2 * (t : ℂ)) • 1) := by
  set D := disagreement a with hD
  set A := (2 * (t : ℂ)) • (1 : Op (Bits n × (B × C))) + D with hA
  have hDpsd : D.PosSemidef := disagreement_psd hn a
  have h2t : (0 : ℝ) < 2 * t := by linarith
  have hApd : A.PosDef := by
    rw [hA, real_smul_eq]
    exact (Matrix.PosDef.one.smul h2t).add_posSemidef hDpsd
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hApd.isUnit
  have hF : filterOperator a t = (2 * (t : ℂ)) • A⁻¹ := rfl
  have hAF : A * filterOperator a t = (2 * (t : ℂ)) • 1 := by
    rw [hF, Matrix.mul_smul, Matrix.mul_nonsing_inv A hdet]
  have hFA : filterOperator a t * A = (2 * (t : ℂ)) • 1 := by
    rw [hF, Matrix.smul_mul, Matrix.nonsing_inv_mul A hdet]
  refine ⟨hApd, ?_, ?_, hAF, hFA⟩
  · rw [hF, real_smul_eq]
    exact hApd.inv.smul h2t
  · -- `1 - F = A⁻¹ (D A) A⁻¹` with `D A = 2t D + D²`.
    unfold Below
    have hDA : (D * A).PosSemidef := by
      have hDD : (D * D).PosSemidef := by
        have := Matrix.posSemidef_conjTranspose_mul_self D
        rwa [hDpsd.isHermitian.eq] at this
      have : D * A = (2 * t : ℝ) • D + D * D := by
        rw [hA, real_smul_eq, mul_add, Matrix.mul_smul, Matrix.mul_one]
      rw [this]
      exact (hDpsd.smul h2t.le).add hDD
    have hconj := hDA.conjTranspose_mul_mul_same A⁻¹
    have hAinvH : (A⁻¹).conjTranspose = A⁻¹ := hApd.inv.isHermitian.eq
    rw [hAinvH] at hconj
    convert hconj using 1
    have hDcomm : D * A = A * D := by
      rw [hA, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    have hDeq : D = A - (2 * (t : ℂ)) • 1 := by rw [hA]; abel
    calc 1 - filterOperator a t = A⁻¹ * A - A⁻¹ * ((2 * (t : ℂ)) • 1) := by
          rw [Matrix.nonsing_inv_mul A hdet, Matrix.mul_smul, Matrix.mul_one, hF]
      _ = A⁻¹ * D := by rw [← Matrix.mul_sub, ← hDeq]
      _ = A⁻¹ * D * (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv A hdet, Matrix.mul_one]
      _ = A⁻¹ * (D * A) * A⁻¹ := by simp only [Matrix.mul_assoc]
