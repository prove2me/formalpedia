-- Prove2me | solution 1 for QAlgorithms.Nannicini.blockEncoding_innerProductDiag
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T11:16:06.767572+00:00
-- url     : https://prove2.me/submissions/98cdb71d-5344-4e7b-90bc-250f6f82698d

import Definitions.Def_QAlgorithms_Nannicini_Ch07a_Model
import Mathlib.LinearAlgebra.UnitaryGroup

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

private lemma permutation_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ ι) :
    ((1 : Matrix ι ι ℂ).submatrix e (Equiv.refl ι)) ∈ Matrix.unitaryGroup ι ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change (1 : Matrix ι ι ℂ).submatrix e (Equiv.refl ι) *
    ((1 : Matrix ι ι ℂ).submatrix e (Equiv.refl ι)).conjTranspose = 1
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
    Matrix.submatrix_mul_equiv, one_mul, Matrix.submatrix_one_equiv e]

private lemma act_ket_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (i j : ι) : act M (ket j) i = M i j := by
  change Matrix.mulVec M (Pi.single j 1) i = M i j
  simp

theorem solution {a p : ℕ}
    (U V : Qubits p → Matrix (Bool × Qubits a) (Bool × Qubits a) ℂ)
    (ψ ψt ϕ ϕt : Qubits p → EuclideanSpace ℂ (Qubits a))
    (hUu : ∀ j, U j ∈ Matrix.unitaryGroup (Bool × Qubits a) ℂ)
    (hVu : ∀ j, V j ∈ Matrix.unitaryGroup (Bool × Qubits a) ℂ)
    (hU : ∀ j, act (U j) (ket (false, fun _ => false)) =
      tensorVec (ket false) (ψ j) + tensorVec (ket true) (ψt j))
    (hV : ∀ j, act (V j) (ket (false, fun _ => false)) =
      tensorVec (ket false) (ϕ j) + tensorVec (ket true) (ϕt j)) :
    IsBlockEncoding ((false, (false, fun _ => false)) : Bool × (Bool × Qubits a))
      ((Matrix.of fun u v : (Bool × (Bool × Qubits a)) × Qubits p =>
          if u.1.1 = v.1.1 ∧ u.2 = v.2 then star (V u.2) u.1.2 v.1.2 else 0) *
        (Matrix.of fun u v : (Bool × (Bool × Qubits a)) × Qubits p =>
          if u.1.1 = v.1.2.1 ∧ u.1.2.1 = v.1.1 ∧ u.1.2.2 = v.1.2.2 ∧ u.2 = v.2 then 1 else 0) *
        (Matrix.of fun u v : (Bool × (Bool × Qubits a)) × Qubits p =>
          if u.1.1 = v.1.1 ∧ u.2 = v.2 then U u.2 u.1.2 v.1.2 else 0))
      1 0 (Matrix.diagonal fun j => inner ℂ (ϕ j) (ψ j)) := by
  classical
  let z : Qubits a := fun _ => false
  let L : Matrix ((Bool × (Bool × Qubits a)) × Qubits p)
      ((Bool × (Bool × Qubits a)) × Qubits p) ℂ := Matrix.of fun u v =>
    if u.1.1 = v.1.1 ∧ u.2 = v.2 then star (V u.2) u.1.2 v.1.2 else 0
  let S : Matrix ((Bool × (Bool × Qubits a)) × Qubits p)
      ((Bool × (Bool × Qubits a)) × Qubits p) ℂ := Matrix.of fun u v =>
    if u.1.1 = v.1.2.1 ∧ u.1.2.1 = v.1.1 ∧ u.1.2.2 = v.1.2.2 ∧ u.2 = v.2 then 1 else 0
  let R : Matrix ((Bool × (Bool × Qubits a)) × Qubits p)
      ((Bool × (Bool × Qubits a)) × Qubits p) ℂ := Matrix.of fun u v =>
    if u.1.1 = v.1.1 ∧ u.2 = v.2 then U u.2 u.1.2 v.1.2 else 0
  let e : ((Bool × (Bool × Qubits a)) × Qubits p) ≃
      (Bool × Qubits p) × (Bool × Qubits a) :=
    { toFun := fun u => ((u.1.1,u.2),u.1.2)
      invFun := fun u => ((u.1.1,u.2),u.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hL : L ∈ Matrix.unitaryGroup _ ℂ := by
    have h := reindex_unitary e _
      (controlled_unitary (fun k : Bool × Qubits p => star (V k.2))
        (fun k => Unitary.star_mem (hVu k.2)))
    convert h using 1
    ext u v
    simp [L,e]
  have hR : R ∈ Matrix.unitaryGroup _ ℂ := by
    have h := reindex_unitary e _
      (controlled_unitary (fun k : Bool × Qubits p => U k.2) (fun k => hUu k.2))
    convert h using 1
    ext u v
    simp [R,e]
  have hS : S ∈ Matrix.unitaryGroup _ ℂ := by
    let sw : ((Bool × (Bool × Qubits a)) × Qubits p) ≃
        ((Bool × (Bool × Qubits a)) × Qubits p) :=
      { toFun := fun u => ((u.1.2.1,(u.1.1,u.1.2.2)),u.2)
        invFun := fun u => ((u.1.2.1,(u.1.1,u.1.2.2)),u.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    convert permutation_unitary sw using 1
    ext u v
    simp [S,sw,Matrix.one_apply,Prod.ext_iff,eq_comm,and_assoc,and_left_comm]
  refine ⟨mul_mem (mul_mem hL hS) hR, ?_⟩
  have hUc (j : Qubits p) (x : Qubits a) : U j (false,x) (false,z) = ψ j x := by
    have h := congrArg (fun f : EuclideanSpace ℂ (Bool × Qubits a) => f (false,x)) (hU j)
    rw [act_ket_apply] at h
    change _ = ((Pi.single false (1 : ℂ) : Bool → ℂ) false) * _ +
      ((Pi.single true (1 : ℂ) : Bool → ℂ) false) * _ at h
    simpa using h
  have hVc (j : Qubits p) (x : Qubits a) : V j (false,x) (false,z) = ϕ j x := by
    have h := congrArg (fun f : EuclideanSpace ℂ (Bool × Qubits a) => f (false,x)) (hV j)
    rw [act_ket_apply] at h
    change _ = ((Pi.single false (1 : ℂ) : Bool → ℂ) false) * _ +
      ((Pi.single true (1 : ℂ) : Bool → ℂ) false) * _ at h
    simpa using h
  have hblock : (Matrix.of fun j k => (L * S * R) ((false,(false,z)),j)
      ((false,(false,z)),k)) = Matrix.diagonal (fun j => inner ℂ (ϕ j) (ψ j)) := by
    ext j k
    by_cases h : j = k
    · subst k
      simp only [Matrix.of_apply, Matrix.diagonal_apply_eq]
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      conv_lhs =>
        simp [L,S,R,Matrix.mul_apply,Fintype.sum_prod_type,Fintype.sum_bool,
          Matrix.conjTranspose_apply,ite_and]
      simp only [hUc,hVc,dotProduct,Pi.star_apply]
      apply Finset.sum_congr rfl
      intro x _
      exact mul_comm _ _
    · simp [L,S,R,Matrix.mul_apply,Fintype.sum_prod_type,h,ite_and]
  change specNorm ((↑(1 : ℝ) : ℂ) • (Matrix.of fun j k =>
    (L * S * R) ((false,(false,z)),j) ((false,(false,z)),k)) - _) ≤ 0
  rw [hblock]
  simp [specNorm]
