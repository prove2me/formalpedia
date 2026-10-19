-- Prove2me | solution 1 for QAlgorithms.Nannicini.blockEncoding_linearCombination
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T11:28:12.992425+00:00
-- url     : https://prove2.me/submissions/0f164148-5c1f-42d2-be0c-ca45cd4b87a9

import Definitions.Def_QAlgorithms_Nannicini_Ch07a_Model
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Module

set_option autoImplicit false
set_option maxHeartbeats 400000
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

private lemma controlled_unitary {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (U : κ → Matrix ι ι ℂ)
    (hU : ∀ k, U k ∈ Matrix.unitaryGroup ι ℂ) :
    (Matrix.of fun y z : κ × ι => if y.1 = z.1 then U y.1 y.2 z.2 else 0) ∈
      Matrix.unitaryGroup (κ × ι) ℂ := by
  classical
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext ⟨k,i⟩ ⟨l,j⟩
  by_cases h : k = l
  · subst l
    have hh := congrArg (fun M : Matrix ι ι ℂ => M i j) (hU k).2
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Matrix.one_apply, eq_comm] using hh
  · simp [Matrix.mul_apply, Fintype.sum_prod_type, h, Ne.symm h]

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

open QAlgorithms.Nannicini
open scoped ComplexConjugate

theorem solution {q a p m : ℕ}
    (Aj : Fin m → Matrix (Qubits q) (Qubits q) ℂ) (y : Fin m → ℂ) (β ξ₁ : ℝ)
    (PL PR : Matrix (Qubits p) (Qubits p) ℂ) (hP : IsStatePrepPair β ξ₁ y PL PR)
    (U : Fin m → Matrix (Qubits a × Qubits q) (Qubits a × Qubits q) ℂ) (α ξ₂ : ℝ)
    (hα : 0 ≤ α) (hξ₂ : 0 ≤ ξ₂)
    (hU : ∀ j, IsBlockEncoding (fun _ => false) (U j) α ξ₂ (Aj j)) :
    IsBlockEncoding ((fun _ => false, fun _ => false) : Qubits p × Qubits a)
      (Matrix.kronecker (Matrix.kronecker (star PL) (1 : Matrix (Qubits a) (Qubits a) ℂ))
          (1 : Matrix (Qubits q) (Qubits q) ℂ) *
        (Matrix.of fun u v : (Qubits p × Qubits a) × Qubits q =>
          if u.1.1 = v.1.1 then
            (if h : bitsToNat u.1.1 < m then U ⟨bitsToNat u.1.1, h⟩ (u.1.2, u.2) (v.1.2, v.2)
              else (1 : Matrix (Qubits a × Qubits q) (Qubits a × Qubits q) ℂ) (u.1.2, u.2)
                (v.1.2, v.2))
          else 0) *
        Matrix.kronecker (Matrix.kronecker PR (1 : Matrix (Qubits a) (Qubits a) ℂ))
          (1 : Matrix (Qubits q) (Qubits q) ℂ))
      (α * β) (α * ξ₁ + max α 1 * β * ξ₂) (∑ j, y j • Aj j) := by
  classical
  let z : Qubits p := fun _ => false
  let w : Qubits a := fun _ => false
  let T (c : Qubits p) : Matrix (Qubits a × Qubits q) (Qubits a × Qubits q) ℂ :=
    Matrix.of fun u v => if h : bitsToNat c < m then U ⟨bitsToNat c,h⟩ u v else (1 : Matrix (Qubits a × Qubits q) (Qubits a × Qubits q) ℂ) u v
  let L := Matrix.kronecker (Matrix.kronecker (star PL) (1 : Matrix (Qubits a) (Qubits a) ℂ))
    (1 : Matrix (Qubits q) (Qubits q) ℂ)
  let R := Matrix.kronecker (Matrix.kronecker PR (1 : Matrix (Qubits a) (Qubits a) ℂ))
    (1 : Matrix (Qubits q) (Qubits q) ℂ)
  let V : Matrix ((Qubits p × Qubits a) × Qubits q) ((Qubits p × Qubits a) × Qubits q) ℂ :=
    Matrix.of fun u v => if u.1.1 = v.1.1 then T u.1.1 (u.1.2,u.2) (v.1.2,v.2) else 0
  have hV : V ∈ Matrix.unitaryGroup _ ℂ := by
    have ht (c : Qubits p) : T c ∈ Matrix.unitaryGroup _ ℂ := by
      by_cases h : bitsToNat c < m
      · have heq : T c = U ⟨bitsToNat c,h⟩ := by ext u v; simp [T,h]
        rw [heq]
        exact (hU _).1
      · have heq : T c = 1 := by ext u v; simp [T,h]
        rw [heq]
        exact one_mem _
    have h := reindex_unitary (Equiv.prodAssoc (Qubits p) (Qubits a) (Qubits q)) _
      (controlled_unitary T ht)
    convert h using 1
    ext u v
    rfl
  have hL : L ∈ Matrix.unitaryGroup _ ℂ :=
    Matrix.kronecker_mem_unitary
      (Matrix.kronecker_mem_unitary (Unitary.star_mem hP.1) (one_mem _)) (one_mem _)
  have hR : R ∈ Matrix.unitaryGroup _ ℂ :=
    Matrix.kronecker_mem_unitary
      (Matrix.kronecker_mem_unitary hP.2.1 (one_mem _)) (one_mem _)
  refine ⟨mul_mem (mul_mem hL hV) hR, ?_⟩
  let c (b : Qubits p) : ℂ := conj (PL b z) * PR b z
  let X (j : Fin m) : Matrix (Qubits q) (Qubits q) ℂ := Matrix.of fun i k => U j (w,i) (w,k)
  have hcol (M : Matrix (Qubits p) (Qubits p) ℂ) (b : Qubits p) :
      act M (zeroKet p) b = M b z := by
    change Matrix.mulVec M (Pi.single z 1) b = _
    simp
  have hb (j : Fin m) : bitsToNat (natToBits p j) = j := by
    rw [← bitsEquivFin_apply]
    simp [natToBits, Nat.mod_eq_of_lt (j.isLt.trans_le hP.2.2.1)]
  have hemb : Function.Injective (fun j : Fin m => natToBits p j) := by
    intro i j h
    apply Fin.ext
    simpa only [hb] using congrArg bitsToNat h
  have hblock : (Matrix.of fun i k => (L * V * R) ((z,w),i) ((z,w),k)) =
      ∑ j : Fin m, c (natToBits p j) • X j := by
    ext i k
    simp only [Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    change _ = ∑ j : Fin m, c (natToBits p j) * U j (w,i) (w,k)
    have hh : (L * V * R) ((z,w),i) ((z,w),k) =
        ∑ b : Qubits p, c b * T b (w,i) (w,k) := by
      simp [L,R,V,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.kroneckerMap_apply,
        Matrix.one_apply,c,mul_assoc,mul_left_comm,mul_comm]
    rw [hh]
    apply Eq.symm
    apply Fintype.sum_of_injective _ hemb _ _
    · intro b hbnot
      have hbm : m ≤ bitsToNat b := by
        by_contra hn
        have hh : natToBits p (⟨bitsToNat b, by omega⟩ : Fin m) = b := natToBits_bitsToNat b
        exact hbnot ⟨_,hh⟩
      have hz : c b = 0 := by simpa only [hcol] using hP.2.2.2.2.2 b hbm
      simp [hz]
    · intro j
      simp [T,hb]
  change specNorm ((↑(α * β) : ℂ) • (Matrix.of fun i k =>
    (L * V * R) ((z,w),i) ((z,w),k)) - _) ≤ _
  rw [hblock]
  change ‖(↑(α * β) : ℂ) • (∑ j : Fin m, c (natToBits p j) • X j) - ∑ j, y j • Aj j‖ ≤ _
  have hc : ∑ j : Fin m, ‖(β : ℂ) * c (natToBits p j) - y j‖ ≤ ξ₁ := by
    simpa only [c,hcol,mul_assoc] using hP.2.2.2.2.1
  have hy : ∑ j : Fin m, ‖y j‖ ≤ β := hP.2.2.2.1
  have hβ : 0 ≤ β := (show 0 ≤ ∑ j : Fin m, ‖y j‖ from
    Finset.sum_nonneg (fun j _ => norm_nonneg (y j))).trans hy
  have hX (j : Fin m) : ‖X j‖ ≤ 1 := compression_contracts w (U j) (hU j).1
  have hE (j : Fin m) : ‖(α : ℂ) • X j - Aj j‖ ≤ ξ₂ := (hU j).2
  have hid : (↑(α * β) : ℂ) • (∑ j : Fin m, c (natToBits p j) • X j) - ∑ j, y j • Aj j =
      ∑ j : Fin m, (((α : ℂ) * ((β : ℂ) * c (natToBits p j) - y j)) • X j +
        y j • ((α : ℂ) • X j - Aj j)) := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [Complex.ofReal_mul,smul_smul,smul_sub,smul_smul,mul_sub,sub_smul]
    module
  rw [hid]
  calc
    _ ≤ ∑ j : Fin m, ‖((α : ℂ) * ((β : ℂ) * c (natToBits p j) - y j)) • X j +
        y j • ((α : ℂ) • X j - Aj j)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin m, (α * ‖(β : ℂ) * c (natToBits p j) - y j‖ + ‖y j‖ * ξ₂) := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ‖((α : ℂ) * ((β : ℂ) * c (natToBits p j) - y j)) • X j‖ +
            ‖y j • ((α : ℂ) • X j - Aj j)‖ := norm_add_le _ _
        _ ≤ α * ‖(β : ℂ) * c (natToBits p j) - y j‖ + ‖y j‖ * ξ₂ := by
          simp only [norm_smul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hα]
          exact add_le_add
            ((mul_le_mul_of_nonneg_left (hX j) (mul_nonneg hα (norm_nonneg _))).trans_eq (mul_one _))
            (mul_le_mul_of_nonneg_left (hE j) (norm_nonneg _))
    _ = α * (∑ j : Fin m, ‖(β : ℂ) * c (natToBits p j) - y j‖) +
        (∑ j : Fin m, ‖y j‖) * ξ₂ := by
      rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul]
    _ ≤ α * ξ₁ + β * ξ₂ := add_le_add (mul_le_mul_of_nonneg_left hc hα)
      (mul_le_mul_of_nonneg_right hy hξ₂)
    _ ≤ α * ξ₁ + max α 1 * β * ξ₂ := by
      nlinarith [le_max_right α 1, mul_nonneg hβ hξ₂]
