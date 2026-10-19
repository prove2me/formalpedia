-- Prove2me | solution 1 for QAlgorithms.Nannicini.blockEncoding_mul
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T11:06:29.19331+00:00
-- url     : https://prove2.me/submissions/39108993-00b2-412c-a7ca-db604bfa08c6

import Definitions.Def_QAlgorithms_Nannicini_Ch07a_Model
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open QAlgorithms
open scoped Matrix.Norms.L2Operator

private lemma reindex_unitary {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    U.submatrix e e ∈ Matrix.unitaryGroup κ ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change U.submatrix e e * (U.submatrix e e).conjTranspose = 1
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  exact (congrArg (fun M : Matrix ι ι ℂ => M.submatrix e e) hU.2).trans
    (Matrix.submatrix_one_equiv e)

private lemma identity_lift_unitary {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    (Matrix.of fun y z : κ × ι => if y.1 = z.1 then U y.2 z.2 else 0) ∈
      Matrix.unitaryGroup (κ × ι) ℂ := by
  have h := Matrix.kronecker_mem_unitary (one_mem (Matrix.unitaryGroup κ ℂ)) hU
  convert h using 1
  ext ⟨k,i⟩ ⟨l,j⟩
  by_cases h : k = l <;> simp [Matrix.kroneckerMap_apply, h]

private lemma compression_contracts {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [Fintype κ] [DecidableEq κ] (z : κ)
    (U : Matrix (κ × ι) (κ × ι) ℂ) (hU : U ∈ Matrix.unitaryGroup (κ × ι) ℂ) :
    ‖(Matrix.of fun i j => U (z,i) (z,j) : Matrix ι ι ℂ)‖ ≤ 1 := by
  classical
  let E : Matrix (κ × ι) ι ℂ := Matrix.of fun u i => if u = (z,i) then 1 else 0
  have hE : E.conjTranspose * E = 1 := by
    ext i j
    simp [E, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, eq_comm]
  have hEnorm : ‖E‖ = 1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self E
    rw [hE, norm_one] at h
    have := norm_nonneg E
    nlinarith
  have heq : (Matrix.of fun i j => U (z,i) (z,j) : Matrix ι ι ℂ) = E.conjTranspose * U * E := by
    ext i j
    simp [E, Matrix.mul_apply, Matrix.conjTranspose_apply]
  let : Nonempty κ := ⟨z⟩
  rw [heq]
  calc
    ‖E.conjTranspose * U * E‖ ≤ ‖E.conjTranspose * U‖ * ‖E‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖E.conjTranspose‖ * ‖U‖) * ‖E‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = 1 := by rw [Matrix.l2_opNorm_conjTranspose, hEnorm, CStarRing.norm_of_mem_unitary hU]; norm_num

theorem solution {q a b : ℕ}
    (UA : Matrix (Qubits a × Qubits q) (Qubits a × Qubits q) ℂ)
    (UB : Matrix (Qubits b × Qubits q) (Qubits b × Qubits q) ℂ)
    (A B : Matrix (Qubits q) (Qubits q) ℂ) (α β ξA ξB : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hA : IsBlockEncoding (fun _ => false) UA α ξA A)
    (hB : IsBlockEncoding (fun _ => false) UB β ξB B) :
    IsBlockEncoding ((fun _ => false, fun _ => false) : Qubits a × Qubits b)
      ((Matrix.of fun y z : (Qubits a × Qubits b) × Qubits q =>
          if y.1.2 = z.1.2 then UA (y.1.1, y.2) (z.1.1, z.2) else 0) *
        (Matrix.of fun y z : (Qubits a × Qubits b) × Qubits q =>
          if y.1.1 = z.1.1 then UB (y.1.2, y.2) (z.1.2, z.2) else 0))
      (α * β) (α * ξB + β * ξA + ξA * ξB) (A * B)  := by
  classical
  let Az : Qubits a := fun _ => false
  let Bz : Qubits b := fun _ => false
  let X : Matrix (Qubits q) (Qubits q) ℂ := Matrix.of fun i j => UA (Az,i) (Az,j)
  let Y : Matrix (Qubits q) (Qubits q) ℂ := Matrix.of fun i j => UB (Bz,i) (Bz,j)
  let L : Matrix ((Qubits a × Qubits b) × Qubits q) ((Qubits a × Qubits b) × Qubits q) ℂ :=
    Matrix.of fun y z => if y.1.2 = z.1.2 then UA (y.1.1,y.2) (z.1.1,z.2) else 0
  let R : Matrix ((Qubits a × Qubits b) × Qubits q) ((Qubits a × Qubits b) × Qubits q) ℂ :=
    Matrix.of fun y z => if y.1.1 = z.1.1 then UB (y.1.2,y.2) (z.1.2,z.2) else 0
  have hL : L ∈ Matrix.unitaryGroup _ ℂ := by
    let e : ((Qubits a × Qubits b) × Qubits q) ≃ Qubits b × (Qubits a × Qubits q) :=
      { toFun := fun y => (y.1.2,y.1.1,y.2)
        invFun := fun y => ((y.2.1,y.1),y.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hh := reindex_unitary e _ (identity_lift_unitary (κ := Qubits b) UA hA.1)
    convert hh using 1
    ext y z
    simp [L, e]
  have hR : R ∈ Matrix.unitaryGroup _ ℂ := by
    have hh := reindex_unitary (Equiv.prodAssoc (Qubits a) (Qubits b) (Qubits q)) _
      (identity_lift_unitary (κ := Qubits a) UB hB.1)
    convert hh using 1
    ext y z
    simp [R]
  refine ⟨mul_mem hL hR, ?_⟩
  have hblock : (Matrix.of fun i j => (L * R) ((Az,Bz),i) ((Az,Bz),j)) = X * Y := by
    ext i j
    simp [L, R, X, Y, Matrix.mul_apply, Fintype.sum_prod_type, eq_comm]
  change specNorm ((↑(α * β) : ℂ) • (Matrix.of fun i j => (L * R) ((Az,Bz),i) ((Az,Bz),j)) - A * B) ≤ _
  rw [hblock]
  change ‖((↑(α * β) : ℂ) • (X * Y) - A * B)‖ ≤ _
  have hX : ‖X‖ ≤ 1 := compression_contracts Az UA hA.1
  have hY : ‖Y‖ ≤ 1 := compression_contracts Bz UB hB.1
  have heA : ‖(α : ℂ) • X - A‖ ≤ ξA := hA.2
  have heB : ‖(β : ℂ) • Y - B‖ ≤ ξB := hB.2
  have hξA : 0 ≤ ξA := (norm_nonneg _).trans heA
  have hξB : 0 ≤ ξB := (norm_nonneg _).trans heB
  have haX : ‖(α : ℂ) • X‖ ≤ α := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hα]
    exact (mul_le_mul_of_nonneg_left hX hα).trans_eq (mul_one α)
  have hbY : ‖(β : ℂ) • Y‖ ≤ β := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ]
    exact (mul_le_mul_of_nonneg_left hY hβ).trans_eq (mul_one β)
  have hBn : ‖B‖ ≤ β + ξB := by
    calc
      ‖B‖ = ‖(β : ℂ) • Y - ((β : ℂ) • Y - B)‖ := by congr 1; abel
      _ ≤ ‖(β : ℂ) • Y‖ + ‖(β : ℂ) • Y - B‖ := norm_sub_le _ _
      _ ≤ β + ξB := add_le_add hbY heB
  have hid : (↑(α * β) : ℂ) • (X * Y) - A * B =
      ((α : ℂ) • X) * ((β : ℂ) • Y - B) + ((α : ℂ) • X - A) * B := by
    rw [Matrix.mul_sub, Matrix.sub_mul, smul_mul_smul_comm, ← Complex.ofReal_mul]
    abel
  rw [hid]
  calc
    _ ≤ ‖((α : ℂ) • X) * ((β : ℂ) • Y - B)‖ + ‖((α : ℂ) • X - A) * B‖ := norm_add_le _ _
    _ ≤ ‖(α : ℂ) • X‖ * ‖(β : ℂ) • Y - B‖ + ‖(α : ℂ) • X - A‖ * ‖B‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ α * ξB + ξA * (β + ξB) := add_le_add
      (mul_le_mul haX heB (norm_nonneg _) hα)
      (mul_le_mul heA hBn (norm_nonneg _) hξA)
    _ = _ := by ring
