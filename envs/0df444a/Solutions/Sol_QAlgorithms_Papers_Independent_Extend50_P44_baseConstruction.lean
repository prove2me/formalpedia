-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P44.baseConstruction
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T12:27:13.803356+00:00
-- url     : https://prove2.me/submissions/7a19c431-dd28-4b4b-ab36-dac92c322603

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Matrix.Block
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker

namespace P038Unitary

theorem rotation_unitary (q : ℝ) (hq : |q| ≤ 1) :
    ((fun b c : Bool => if b = c then (q : ℂ)
      else -Complex.I * (Real.sqrt (1 - q ^ 2) : ℂ)) : Matrix Bool Bool ℂ) ∈
      Matrix.unitaryGroup Bool ℂ := by
  have hq2 : q ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one q).mpr hq
  have hs : (Real.sqrt (1 - q ^ 2)) ^ 2 = 1 - q ^ 2 :=
    Real.sq_sqrt (sub_nonneg.mpr hq2)
  have hsc : (Real.sqrt (1 - q ^ 2) : ℂ) ^ 2 = 1 - (q : ℂ) ^ 2 := by
    exact_mod_cast hs
  apply Matrix.mem_unitaryGroup_iff'.mpr
  ext i j
  change (∑ k : Bool, star (if k = i then (q : ℂ)
      else -Complex.I * (Real.sqrt (1 - q ^ 2) : ℂ)) *
      (if k = j then (q : ℂ) else -Complex.I * (Real.sqrt (1 - q ^ 2) : ℂ))) =
    if i = j then 1 else 0
  cases i <;> cases j <;> apply Complex.ext <;>
    simp [Fintype.sum_bool, Complex.mul_re, Complex.mul_im] <;> nlinarith

theorem blockDiagonal_unitary {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (M : κ → Matrix ι ι ℂ) (hM : ∀ k, M k ∈ Matrix.unitaryGroup ι ℂ) :
    Matrix.blockDiagonal M ∈ Matrix.unitaryGroup (ι × κ) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  simp only [Matrix.star_eq_conjTranspose, Matrix.blockDiagonal_conjTranspose,
    ← Matrix.blockDiagonal_mul]
  have h : (fun k => (M k)ᴴ * M k) = 1 := by
    funext k
    exact (hM k).1
  rw [h, Matrix.blockDiagonal_one]

theorem rangeFlip_unitary (valid : Bool) :
    ((fun b c : Bool => if b = (if valid then c else !c) then (1 : ℂ) else 0) :
      Matrix Bool Bool ℂ) ∈
      Matrix.unitaryGroup Bool ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  ext i j
  change (∑ k : Bool,
      star (if k = (if valid then i else !i) then (1 : ℂ) else 0) *
      (if k = (if valid then j else !j) then (1 : ℂ) else 0)) =
    if i = j then 1 else 0
  cases valid <;> cases i <;> cases j <;>
    simp [Fintype.sum_bool]

theorem flagged_rotation_unitary {κ : Type*} [Fintype κ] [DecidableEq κ]
    (q : κ → ℝ) (hq : ∀ k, |q k| ≤ 1) (valid : κ → Bool) :
    (fun x y : (Bool × Bool) × κ =>
      if x.2 = y.2 ∧ x.1.2 = (if valid y.2 then y.1.2 else !y.1.2) then
        (if x.1.1 = y.1.1 then (q y.2 : ℂ)
          else -Complex.I * (Real.sqrt (1 - q y.2 ^ 2) : ℂ)) else 0) ∈
      Matrix.unitaryGroup ((Bool × Bool) × κ) ℂ := by
  let R (k : κ) : Matrix Bool Bool ℂ := fun b c =>
    if b = c then (q k : ℂ) else -Complex.I * (Real.sqrt (1 - q k ^ 2) : ℂ)
  let F (k : κ) : Matrix Bool Bool ℂ := fun b c =>
    if b = (if valid k then c else !c) then 1 else 0
  let A : Matrix ((Bool × Bool) × κ) ((Bool × Bool) × κ) ℂ := fun x y =>
      if x.2 = y.2 ∧ x.1.2 = (if valid y.2 then y.1.2 else !y.1.2) then
        (if x.1.1 = y.1.1 then (q y.2 : ℂ)
          else -Complex.I * (Real.sqrt (1 - q y.2 ^ 2) : ℂ)) else 0
  have h : Matrix.blockDiagonal (fun k => R k ⊗ₖ F k) ∈
      Matrix.unitaryGroup ((Bool × Bool) × κ) ℂ :=
    blockDiagonal_unitary _ fun k =>
      Matrix.kronecker_mem_unitary (rotation_unitary (q k) (hq k)) (rangeFlip_unitary (valid k))
  change A ∈ Matrix.unitaryGroup ((Bool × Bool) × κ) ℂ
  have heq : A = Matrix.blockDiagonal (fun k => R k ⊗ₖ F k) := by
    ext x y
    by_cases hxy : x.2 = y.2
    · simp [Matrix.blockDiagonal_apply, Matrix.kronecker_apply, A, R, F, hxy,
        Matrix.kronecker, Matrix.kroneckerMap, mul_ite]
    · simp [Matrix.blockDiagonal_apply, A, hxy]
  rw [heq]
  exact h

theorem tableAbs_le_foldMax {D : ℕ} (a : Fin D → ℝ) (j : Fin D) :
    |a j| ≤ (List.ofFn fun k => |a k|).foldr max 0 := by
  exact List.le_max_of_le' 0 (List.mem_ofFn.mpr ⟨j, rfl⟩) le_rfl

theorem normalized_table_bound {D : ℕ} (a : Fin D → ℝ)
    (ha : 0 < (List.ofFn fun k => |a k|).foldr max 0) (j : Fin D) :
    |a j / (List.ofFn fun k => |a k|).foldr max 0| ≤ 1 := by
  rw [abs_div, abs_of_pos ha, div_le_one ha]
  exact tableAbs_le_foldMax a j

end P038Unitary



noncomputable section
open scoped Matrix ComplexConjugate BigOperators

namespace P038Aux

variable {X Y Z : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]

def equivMatrix (e : X ≃ Y) : Matrix Y X ℂ :=
  fun y x => if e x = y then 1 else 0

theorem equivMatrix_mul (e : X ≃ Y) (A : Matrix X Z ℂ) :
    equivMatrix e * A = A.submatrix e.symm id := by
  ext y z
  simp [Matrix.mul_apply, equivMatrix, ← e.eq_symm_apply]

theorem mul_equivMatrix (e : X ≃ Y) (A : Matrix Z Y ℂ) :
    A * equivMatrix e = A.submatrix id e := by
  ext z x
  simp [Matrix.mul_apply, equivMatrix, mul_ite]

theorem equivMatrix_conjTranspose (e : X ≃ Y) :
    (equivMatrix e)ᴴ = equivMatrix e.symm := by
  ext x y
  simp [equivMatrix, Matrix.conjTranspose_apply, e.symm_apply_eq, eq_comm]

theorem equivMatrix_star_mul (e : X ≃ Y) :
    (equivMatrix e)ᴴ * equivMatrix e = 1 := by
  rw [equivMatrix_conjTranspose, equivMatrix_mul]
  ext x y
  simp [equivMatrix, Matrix.one_apply, eq_comm]

theorem equivMatrix_mul_star (e : X ≃ Y) :
    equivMatrix e * (equivMatrix e)ᴴ = 1 := by
  rw [equivMatrix_conjTranspose, equivMatrix_mul]
  ext x y
  simp [equivMatrix, Matrix.one_apply, eq_comm]

theorem equivMatrix_sandwich (e f : X ≃ Y) (A : Matrix X X ℂ) :
    equivMatrix e * A * (equivMatrix f)ᴴ = A.submatrix e.symm f.symm := by
  rw [equivMatrix_conjTranspose, equivMatrix_mul, mul_equivMatrix]
  rfl

theorem submatrix_unitary {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (e f : Y ≃ X)
    (A : Matrix X X ℂ) (hA : A ∈ Matrix.unitaryGroup X ℂ) :
    A.submatrix e f ∈ Matrix.unitaryGroup Y ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (A.submatrix e f)ᴴ * A.submatrix e f = 1
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  rw [show Aᴴ * A = 1 from hA.1]
  ext i j
  simp [Matrix.one_apply]

section Diffusion

variable {F S I : Type*} [Fintype F] [Fintype S] [Fintype I]
  [DecidableEq F] [DecidableEq S] [DecidableEq I]

def liftDiffusion (H : Matrix S S ℂ) : Matrix (F × (S × I)) (F × (S × I)) ℂ :=
  fun x y => if x.1 = y.1 ∧ x.2.2 = y.2.2 then H x.2.1 y.2.1 else 0

open scoped Kronecker in
theorem liftDiffusion_unitary (H : Matrix S S ℂ)
    (hH : H ∈ Matrix.unitaryGroup S ℂ) :
    liftDiffusion (F := F) (I := I) H ∈ Matrix.unitaryGroup (F × (S × I)) ℂ := by
  have h : liftDiffusion (F := F) (I := I) H =
      (1 : Matrix F F ℂ) ⊗ₖ (H ⊗ₖ (1 : Matrix I I ℂ)) := by
    ext x y
    by_cases hf : x.1 = y.1 <;> by_cases hi : x.2.2 = y.2.2 <;>
      simp [liftDiffusion, Matrix.kronecker_apply, Matrix.one_apply, hf, hi]
  rw [h]
  exact Matrix.kronecker_mem_unitary (one_mem _)
    (Matrix.kronecker_mem_unitary hH (one_mem _))

end Diffusion

section SelectedBlock

variable {L S I : Type*} [Fintype L] [Fintype S] [Fintype I]
  [DecidableEq L] [DecidableEq S] [DecidableEq I]

def rangeControlled (R : L → Matrix Bool Bool ℂ) (v : L → Bool) :
    Matrix ((Bool × Bool) × L) ((Bool × Bool) × L) ℂ :=
  fun x y => if x.2 = y.2 ∧ x.1.2 = (if v y.2 then y.1.2 else !y.1.2) then
    R y.2 x.1.1 y.1.1 else 0

abbrev matrixProduct {J K M : Type*} [Fintype K]
    (A : Matrix J K ℂ) (B : Matrix K M ℂ) : Matrix J M ℂ :=
  @HMul.hMul (Matrix J K ℂ) (Matrix K M ℂ) (Matrix J M ℂ)
    Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

def prepared (e : L ≃ (S × I)) (H : Matrix S S ℂ) :
    Matrix ((Bool × Bool) × L) ((Bool × Bool) × (S × I)) ℂ :=
  (equivMatrix (Equiv.prodCongr (Equiv.refl (Bool × Bool)) e))ᴴ *
    liftDiffusion H

theorem prepared_eq_native (e : L ≃ (S × I)) (H : Matrix S S ℂ) :
    prepared e H =
      matrixProduct (equivMatrix (Equiv.prodCongr (Equiv.refl (Bool × Bool)) e))ᴴ
        (liftDiffusion (F := Bool × Bool) (I := I) H) := by
  rfl

theorem prepared_apply (e : L ≃ (S × I)) (H : Matrix S S ℂ)
    (x : (Bool × Bool) × L) (y : (Bool × Bool) × (S × I)) :
    prepared e H x y =
      if x.1 = y.1 ∧ (e x.2).2 = y.2.2 then H (e x.2).1 y.2.1 else 0 := by
  rw [prepared_eq_native]
  unfold matrixProduct
  rw [equivMatrix_conjTranspose, equivMatrix_mul]
  rfl

theorem rangeControlled_prepared_apply (R : L → Matrix Bool Bool ℂ) (v : L → Bool)
    (e : L ≃ (S × I)) (H : Matrix S S ℂ) (z : S)
    (x : (Bool × Bool) × L) (j : I) :
    (rangeControlled R v * prepared e H) x ((false, false), (z, j)) =
      if x.1.2 = (if v x.2 then false else true) ∧ (e x.2).2 = j then
        R x.2 x.1.1 false * H (e x.2).1 z else 0 := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool,
    prepared_apply, rangeControlled]
  simp [ite_and, ite_mul, mul_ite]
  rw [Finset.sum_eq_single x.2]
  · by_cases hf : x.1.2 = !v x.2 <;> by_cases he : (e x.2).2 = j <;>
      simp [hf, he]
  · intro l hl hne
    simp [Ne.symm hne]
  · simp

theorem selected_block (R : L → Matrix Bool Bool ℂ) (v : L → Bool)
    (er ec : L ≃ (S × I)) (Hr Hc : Matrix S S ℂ) (z : S) (i j : I) :
    ((prepared er Hr)ᴴ * rangeControlled R v * prepared ec Hc)
        ((false, false), (z, i)) ((false, false), (z, j)) =
      ∑ l : L, if v l = true ∧ (er l).2 = i ∧ (ec l).2 = j then
        star (Hr (er l).1 z) * R l false false * Hc (ec l).1 z else 0 := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, prepared_apply,
    rangeControlled_prepared_apply, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false,
    false_and, and_false, true_and, and_true, ite_false, star_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add]
  apply Finset.sum_congr rfl
  intro l hl
  cases hv : v l <;> by_cases hr : (er l).2 = i <;>
    by_cases hc : (ec l).2 = j <;> simp [hv, hr, hc, mul_assoc]

theorem prepared_sandwich_eq (er ec : L ≃ (S × I)) (Hr Hc : Matrix S S ℂ)
    (K : Matrix ((Bool × Bool) × L) ((Bool × Bool) × L) ℂ) :
    (prepared er Hr)ᴴ * K * prepared ec Hc =
      (liftDiffusion Hr)ᴴ *
        K.submatrix (Equiv.prodCongr (Equiv.refl (Bool × Bool)) er).symm
          (Equiv.prodCongr (Equiv.refl (Bool × Bool)) ec).symm *
        liftDiffusion Hc := by
  calc
    _ = (liftDiffusion Hr)ᴴ *
          (equivMatrix (Equiv.prodCongr (Equiv.refl (Bool × Bool)) er) * K *
          (equivMatrix (Equiv.prodCongr (Equiv.refl (Bool × Bool)) ec))ᴴ) *
          liftDiffusion Hc := by
      rw [prepared_eq_native, prepared_eq_native]
      unfold matrixProduct
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [equivMatrix_sandwich]

theorem prepared_sandwich_unitary (er ec : L ≃ (S × I)) (Hr Hc : Matrix S S ℂ)
    (hr : Hr ∈ Matrix.unitaryGroup S ℂ) (hc : Hc ∈ Matrix.unitaryGroup S ℂ)
    (K : Matrix ((Bool × Bool) × L) ((Bool × Bool) × L) ℂ)
    (hk : K ∈ Matrix.unitaryGroup ((Bool × Bool) × L) ℂ) :
    (prepared er Hr)ᴴ * K * prepared ec Hc ∈
      Matrix.unitaryGroup ((Bool × Bool) × (S × I)) ℂ := by
  rw [prepared_sandwich_eq]
  apply mul_mem
  · apply mul_mem
    · exact Unitary.star_mem (liftDiffusion_unitary Hr hr)
    · exact submatrix_unitary _ _ K hk
  · exact liftDiffusion_unitary Hc hc

end SelectedBlock

end P038Aux


namespace Prove2MeS03

/-- Cancellation of the supported sparsity and data normalizations. -/
theorem base_normalization (Sc Sr : ℕ) (hSc : 0 < Sc) (hSr : 0 < Sr)
    (t x : ℝ) (ht : 0 < t) :
    ((Real.sqrt ((Sc : ℝ) * Sr) * t : ℝ) : ℂ) *
      (star ((Real.sqrt (Sr : ℝ))⁻¹ : ℂ) * (x / t : ℂ) *
        ((Real.sqrt (Sc : ℝ))⁻¹ : ℂ)) = (x : ℂ) := by
  have hc : 0 < (Sc : ℝ) := Nat.cast_pos.mpr hSc
  have hr : 0 < (Sr : ℝ) := Nat.cast_pos.mpr hSr
  have hc0 : Real.sqrt (Sc : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hr0 : Real.sqrt (Sr : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  have ht0 : t ≠ 0 := ht.ne'
  have hreal : Real.sqrt ((Sc : ℝ) * Sr) * t *
      ((Real.sqrt (Sr : ℝ))⁻¹ * (x / t) * (Real.sqrt (Sc : ℝ))⁻¹) = x := by
    rw [Real.sqrt_mul hc.le]
    field_simp
    <;> ring
  simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_div,
    map_inv₀, Complex.star_def, Complex.conj_ofReal] using
    congrArg (fun r : ℝ => (r : ℂ)) hreal

/-- Two Boolean flags contribute two ancilla bits. -/
theorem base_ancilla_card (s : ℕ) :
    Fintype.card ((Bool × Bool) × Fin (2 ^ s)) = 2 ^ (s + 2) := by
  simp [Fintype.card_prod, pow_add, Nat.mul_comm]


end Prove2MeS03

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix
open P038Aux

variable {n s d m : ℕ}

theorem p038_withFlags_eq {F X Y : Type*} [DecidableEq F]
    [DecidableEq X] [DecidableEq Y] (e : X ≃ Y) :
    withFlags (F := F) e =
      equivMatrix (Equiv.prodCongr (Equiv.refl F) e) := by
  ext x y
  by_cases hf : x.1 = y.1 <;> by_cases he : x.2 = e y.2 <;>
    simp [withFlags, equivMatrix,
      QAlgorithms.Papers.Independent.Information100.P34.permutationMatrix,
      hf, he, eq_comm, Prod.ext_iff, Prod.map]

theorem p038_middle_eq (B : Scheme n s d m) (a : Fin (2 ^ d) → ℝ) :
    B.baseMiddle a false =
      rangeControlled (fun l => dataRotation (a l.1 / tableMax a)) B.valid := by
  ext x y
  simp [Scheme.baseMiddle, rangeControlled]

set_option backward.isDefEq.respectTransparency.types false in
theorem p038_middle_unitary (B : Scheme n s d m) (a : Fin (2 ^ d) → ℝ)
    (ha : 0 < tableMax a) :
    B.baseMiddle a false ∈
      Matrix.unitaryGroup ((Bool × Bool) × (Fin (2 ^ d) × Fin (2 ^ m))) ℂ := by
  convert P038Unitary.flagged_rotation_unitary
    (fun l : Fin (2 ^ d) × Fin (2 ^ m) => a l.1 / tableMax a)
    (fun l => P038Unitary.normalized_table_bound a ha l.1) B.valid using 1
  all_goals first | rfl | (apply heq_of_eq; ext x y; simp [Scheme.baseMiddle, dataRotation])

theorem p038_circuit_eq_native (B : Scheme n s d m) (a : Fin (2 ^ d) → ℝ) :
    B.baseCircuit a =
      (matrixProduct
        (matrixProduct
          (matrixProduct
            (matrixProduct (diffusion (n := n) (F := Bool × Bool) B.Hr)ᴴ
              (withFlags (F := Bool × Bool) B.row))
            (B.baseMiddle a false))
          (withFlags (F := Bool × Bool) B.column)ᴴ)
        (diffusion (n := n) (F := Bool × Bool) B.Hc)).submatrix
        (Equiv.prodAssoc (Bool × Bool) (Fin (2 ^ s)) (Fin (2 ^ n)))
        (Equiv.prodAssoc (Bool × Bool) (Fin (2 ^ s)) (Fin (2 ^ n))) := by
  rfl

theorem p038_circuit_eq (B : Scheme n s d m) (a : Fin (2 ^ d) → ℝ) :
    B.baseCircuit a =
      ((prepared B.row B.Hr)ᴴ * B.baseMiddle a false * prepared B.column B.Hc).submatrix
        (Equiv.prodAssoc (Bool × Bool) (Fin (2 ^ s)) (Fin (2 ^ n)))
        (Equiv.prodAssoc (Bool × Bool) (Fin (2 ^ s)) (Fin (2 ^ n))) := by
  rw [p038_circuit_eq_native, prepared_eq_native, prepared_eq_native]
  unfold matrixProduct
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [p038_withFlags_eq, Matrix.mul_assoc]
  rfl

theorem p038_circuit_unitary (B : Scheme n s d m) (a : Fin (2 ^ d) → ℝ)
    (ha : 0 < tableMax a) :
    B.baseCircuit a ∈
      Matrix.unitaryGroup (((Bool × Bool) × Fin (2 ^ s)) × Fin (2 ^ n)) ℂ := by
  rw [p038_circuit_eq]
  apply submatrix_unitary
  exact prepared_sandwich_unitary B.row B.column B.Hr B.Hc
    B.Hr_unitary B.Hc_unitary (B.baseMiddle a false) (p038_middle_unitary B a ha)

theorem p038_circuit_selected (B : Scheme n s d m) (a : Fin (2 ^ d) → ℝ)
    (i j : Fin (2 ^ n)) :
    B.baseCircuit a false (((false, false), 0), i) (((false, false), 0), j) =
      ∑ l : Fin (2 ^ d) × Fin (2 ^ m),
        if B.valid l = true ∧ (B.row l).2 = i ∧ (B.column l).2 = j then
          star (B.Hr (B.row l).1 0) * (a l.1 / tableMax a : ℂ) *
            B.Hc (B.column l).1 0 else 0 := by
  rw [p038_circuit_eq, p038_middle_eq]
  simpa [Matrix.submatrix_apply, dataRotation] using
    selected_block (fun l => dataRotation (a l.1 / tableMax a)) B.valid
      B.row B.column B.Hr B.Hc 0 i j

theorem p038_normalization (B : Scheme n s d m) (a : Fin (2 ^ d) → ℝ)
    (ha : 0 < tableMax a) (l : Fin (2 ^ d) × Fin (2 ^ m))
    (hl : B.valid l = true) :
    (B.baseAlpha a : ℂ) *
      (star (B.Hr (B.row l).1 0) * (a l.1 / tableMax a : ℂ) *
        B.Hc (B.column l).1 0) = (a l.1 : ℂ) := by
  rw [B.Hr_zero, B.Hc_zero]
  simp only [if_pos (B.row_range l hl), if_pos (B.column_range l hl)]
  simpa only [Scheme.baseAlpha] using Prove2MeS03.base_normalization
    B.columnSlots.card B.rowSlots.card
    (Finset.card_pos.mpr B.column_nonempty) (Finset.card_pos.mpr B.row_nonempty)
    (tableMax a) (a l.1) ha

theorem p038_block_identity (B : Scheme n s d m) (a : Fin (2 ^ d) → ℝ)
    (ha : 0 < tableMax a) :
    (B.baseAlpha a : ℂ) •
      (Matrix.of fun i j : Fin (2 ^ n) =>
        B.baseCircuit a false (((false, false), 0), i) (((false, false), 0), j)) =
      B.matrix a := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
    p038_circuit_selected, Scheme.matrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases h : B.valid l = true ∧ (B.row l).2 = i ∧ (B.column l).2 = j
  · simp only [if_pos h]
    exact p038_normalization B a ha l h.1
  · simp [h]

end QAlgorithms.Papers.Independent.Extend50.P44

open QAlgorithms.Papers.Independent.Extend50.P44

theorem solution {n s d m : ℕ} (B : Scheme n s d m) (a : Fin (2 ^ d) → ℝ)
    (active : Finset (Fin (2 ^ d))) (hactive : active.Nonempty)
    (hpadding : ∀ j, j ∉ active → a j = 0)
    (ha : 0 < tableMax a) :
    QAlgorithms.IsBlockEncoding ((false, false), 0) (B.baseCircuit a)
      (B.baseAlpha a) 0 (B.matrix a) ∧
    loadingCost (baseLoadingSchedule active.card) = active.card ∧
    Fintype.card ((Bool × Bool) × Fin (2 ^ s)) = 2 ^ (s + 2) := by
  refine ⟨⟨p038_circuit_unitary B a ha, ?_⟩, ?_, ?_⟩
  · rw [p038_block_identity B a ha, sub_self, QAlgorithms.specNorm]
    letI : NormedAddCommGroup (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
      Matrix.instL2OpNormedAddCommGroup
    exact le_of_eq norm_zero
  · simp [loadingCost, baseLoadingSchedule]
  · exact Prove2MeS03.base_ancilla_card s

#print axioms solution
