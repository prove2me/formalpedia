-- Prove2me | solution 1 for QuantumSDP18.MeasureBE.cnot_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:10:01.053783+00:00
-- url     : https://prove2.me/submissions/ae6bafa9-c0dd-4d42-b9e1-f494d2fb637b

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumSDP18_MeasureBE_Setting

set_option autoImplicit false
open QuantumSDP18.MeasureBE

lemma cnot_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℕ) (x x' : ι × Anc c) :
    cnotLast (ι := ι) c (x, false) (x', false) = if x = x' ∧ x.2.2 = false then 1 else 0 := by
  obtain ⟨s, c1, b⟩ := x
  obtain ⟨s', c1', b'⟩ := x'
  simp only [cnotLast, cnotRegs, Matrix.reindex_apply, Equiv.symm_mk, Equiv.coe_fn_mk,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, QAlgorithms.cnot,
    Matrix.of_apply, Prod.mk.injEq]
  cases b <;> cases b' <;> simp

lemma W_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℕ) (U : Matrix (ι × Anc c) (ι × Anc c) ℂ)
    (x : ι × Anc c) (t : Bool) (i : ι) :
    (Uprime c U * ketZeroPrime (ι := ι) c) (x, t) i = if t = false then U x (i, ancZero c) else 0 := by
  simp only [Matrix.mul_apply, Uprime, ketZeroPrime, Matrix.kroneckerMap_apply, Matrix.of_apply,
    Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (i, ancZero c)]
  · cases t <;> simp
  · intro y _ hy
    simp [hy]
  · simp

lemma K_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℕ) (U : Matrix (ι × Anc c) (ι × Anc c) ℂ)
    (x : ι × Anc c) (i : ι) :
    (U * ketZero (ι := ι) c) x i = U x (i, ancZero c) := by
  simp only [Matrix.mul_apply, ketZero, Matrix.of_apply]
  rw [Finset.sum_eq_single (i, ancZero c)]
  · simp
  · intro y _ hy
    have : ¬ (y.1 = i ∧ y.2 = ancZero c) := fun h => hy (Prod.ext h.1 h.2)
    simp [this]
  · simp

lemma abs_sum {Y I : Type*} [Fintype Y] [Fintype I] [DecidableEq Y] (u : Y → I → ℂ)
    (C : Matrix (Y × Bool) (Y × Bool) ℂ) (P : Y → Prop) [DecidablePred P]
    (hC : ∀ x x', C (x, false) (x', false) = if x = x' ∧ P x then 1 else 0)
    (W : Matrix (Y × Bool) I ℂ) (hW : ∀ x t i, W (x, t) i = if t = false then u x i else 0)
    (i j : I) :
    (W.conjTranspose * C * W) i j = ∑ x, if P x then star (u x i) * u x j else 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, hW]
  simp only [hC, Bool.true_eq_false, if_false, if_true, star_zero, zero_mul, mul_zero, add_zero,
    Finset.sum_const_zero, zero_add, eq_self_iff_true]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_eq_single x]
  · by_cases h : P x <;> simp [h]
  · intro y _ hy
    simp [hy]
  · simp

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℕ)
    (U : Matrix (ι × Anc c) (ι × Anc c) ℂ) :
    blockK c U = (ketZeroPrime (ι := ι) c).conjTranspose * (Uprime c U).conjTranspose *
      cnotLast (ι := ι) c * Uprime c U * ketZeroPrime (ι := ι) c := by
  have hL : blockK c U = ((U * ketZero (ι := ι) c).conjTranspose * accProj (ι := ι) c *
      (U * ketZero (ι := ι) c)) := by
    unfold blockK
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hR : (ketZeroPrime (ι := ι) c).conjTranspose * (Uprime c U).conjTranspose *
      cnotLast (ι := ι) c * Uprime c U * ketZeroPrime (ι := ι) c =
      (Uprime c U * ketZeroPrime (ι := ι) c).conjTranspose * cnotLast (ι := ι) c *
        (Uprime c U * ketZeroPrime (ι := ι) c) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hL, hR]
  ext i j
  rw [abs_sum (fun x i => U x (i, ancZero c)) (cnotLast (ι := ι) c) (fun x => x.2.2 = false)
    (fun x x' => cnot_entry c x x') (Uprime c U * ketZeroPrime (ι := ι) c) (W_entry c U)]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [accProj, Matrix.mul_diagonal, Matrix.conjTranspose_apply, K_entry]
  by_cases h : x.2.2 = false <;> simp [h]
