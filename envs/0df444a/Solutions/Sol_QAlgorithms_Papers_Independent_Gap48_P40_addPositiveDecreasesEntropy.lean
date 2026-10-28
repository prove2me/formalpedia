-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.addPositiveDecreasesEntropy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T08:55:20.553678+00:00
-- url     : https://prove2.me/submissions/01ce2615-9600-4d91-8c17-ee9270a93442

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12
import Theorems.Thm_SimpleSSA_Monotone_eq_4
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

section X5mod_OL_Base
open Matrix
open scoped ComplexOrder

namespace X5OL

variable {I : Type*} [Fintype I] [DecidableEq I]

end X5OL
end X5mod_OL_Base

section X5mod_B2_Main
open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace X5B2

section Scalar
variable {ι : Type*} [Fintype ι]
variable {l m : ι → ℝ} {W : ι → ι → ℝ}

variable (hW : ∀ i j, 0 ≤ W i j) (hcol : ∀ j, ∑ i, W i j = 1) (hl : ∀ j, 0 ≤ l j)
  (hm : ∀ i, 0 ≤ m i) (hs : ∀ i j, W i j ≠ 0 → l j ≠ 0 → m i ≠ 0)

end Scalar

section Mat
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma fin (X : Matrix I I ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum (A := X)).continuousOn f

end Mat

end X5B2

namespace X5B2
open QAlgorithms.Papers.Independent.Claimed50.P12

variable {I : Type*} [Fintype I] [DecidableEq I]

end X5B2
end X5mod_B2_Main

section X5mod_UH_Base
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder

namespace X5UH
set_option linter.unusedSectionVars false

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

end X5UH
end X5mod_UH_Base

section X5mod_UH_Polar
open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace X5UH
set_option linter.unusedSectionVars false

variable {R : Type*} [Fintype R] [DecidableEq R]

end X5UH
end X5mod_UH_Polar

section X5mod_UH_Main
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate

namespace X5UH
set_option linter.unusedSectionVars false

variable {D R : Type*} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

end X5UH
end X5mod_UH_Main

section X5mod_UH_Thm
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate

namespace X5UH
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Information100.P32 (Op)
set_option linter.unusedSectionVars false

variable {D R : Type*} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

end X5UH
end X5mod_UH_Thm

section X5mod_UH_B4
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5UH
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Information100.P32 (Op)
set_option linter.unusedSectionVars false

variable {D E X : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
  [Fintype X] [DecidableEq X]

end X5UH
end X5mod_UH_B4

section X5mod_UH_B5
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5UH
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Information100.P32 (Op)
set_option linter.unusedSectionVars false

variable {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R]

end X5UH
end X5mod_UH_B5

section X5mod_UH_B8a
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5UH
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Information100.P32 (Op)
set_option linter.unusedSectionVars false

variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

end X5UH
end X5mod_UH_B8a

section X5mod_UH_B8
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5UH
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Information100.P32 (Op)
set_option linter.unusedSectionVars false

variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

end X5UH
end X5mod_UH_B8

section X5mod_AI_Base
open Matrix

section X5mod_AI_Base

end X5mod_AI_Base
end X5mod_AI_Base

section X5mod_AD_Kron
open Matrix Polynomial
open scoped ComplexOrder Kronecker

namespace X5AD
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

end X5AD
end X5mod_AD_Kron

section X5mod_QC_Emb
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
set_option linter.unusedSectionVars false

variable {m n K : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype K]
  [DecidableEq K]

/-- A family of orthogonal multiplicative embeddings. -/
structure OEmb (E : K → Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) : Prop where
  mul : ∀ b c Y Z, E b Y * E c Z = if b = c then E b (Y * Z) else 0
  star : ∀ b Y, (E b Y)ᴴ = E b Yᴴ

variable {E : K → Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ}

end X5QC

namespace X5QC
set_option linter.unusedSectionVars false
variable {m n B : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype B]
  [DecidableEq B]

end X5QC
end X5mod_QC_Emb

section X5mod_QC_Kron
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

end X5QC
end X5mod_QC_Kron

section X5mod_QC_Supp
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

end X5QC
end X5mod_QC_Supp

section X5mod_QC_Qcq
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)
set_option linter.unusedSectionVars false

variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

variable (U : Matrix B B ℂ) (p : B → ℝ) (rho : B → Matrix (A × C) (A × C) ℂ)

end X5QC
end X5mod_QC_Qcq

section X5mod_QC_Ent
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma real_smul (p : ℝ) (Y : Matrix ι ι ℂ) : (p : ℂ) • Y = p • Y := by
  ext i j; simp [Complex.real_smul]

end X5QC
end X5mod_QC_Ent

section X5mod_QC_Blk
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
set_option linter.unusedSectionVars false

section gen
variable {m n K : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype K]
  [DecidableEq K] {E : K → Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ}

end gen

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma mul_log (X : Matrix ι ι ℂ) (hX : X.IsHermitian) :
    X * cfc Real.log X = cfc (fun x : ℝ => x * Real.log x) X := by
  nth_rewrite 1 [← cfc_id' ℝ X hX.isSelfAdjoint]
  rw [← cfc_mul _ _ _ (X5B2.fin _ _) (X5B2.fin _ _)]

end X5QC
end X5mod_QC_Blk

section X5mod_QC_Main
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)
set_option linter.unusedSectionVars false

variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]
variable {U : Matrix B B ℂ} (hU : Uᴴ * U = 1) {p : B → ℝ} (hp : ∀ b, 0 ≤ p b)
  {rho : B → Matrix (A × C) (A × C) ℂ} (hrho : ∀ b, QAlgorithms.IsDensityMatrix (rho b))
include hU hp hrho

end X5QC
end X5mod_QC_Main

section X5mod_QC_Thm
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)
set_option linter.unusedSectionVars false

variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

variable (U : Matrix B B ℂ) (p : B → ℝ) (rho : B → Matrix (A × C) (A × C) ℂ)

end X5QC
end X5mod_QC_Thm

section X5mod_QC_Final
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)
set_option linter.unusedSectionVars false

variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

end X5QC
end X5mod_QC_Final

section X5mod_QC_Conc
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)
set_option linter.unusedSectionVars false

variable {A B X : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype X] [DecidableEq X]

variable (p : X → ℝ) (rho : X → Matrix (A × B) (A × B) ℂ)

variable {p rho}

end X5QC
end X5mod_QC_Conc

section X5mod_QC_Mix
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)
set_option linter.unusedSectionVars false

variable {A X : Type*} [Fintype A] [DecidableEq A] [Fintype X] [DecidableEq X]

variable (p : X → ℝ) (rho : X → Matrix A A ℂ)

variable {p rho}

end X5QC
end X5mod_QC_Mix

section X5mod_AF_Bounds
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5AF
open X5QC
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma tr_cfc {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    (cfc f X).trace = ∑ i, ((f (hX.eigenvalues i) : ℝ) : ℂ) := by
  rw [hX.cfc_eq]
  unfold IsHermitian.cfc
  simp only [Unitary.conjStarAlgAut_apply]
  set U := (hX.eigenvectorUnitary : Matrix ι ι ℂ)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem (hX.eigenvectorUnitary).2
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.trace_diagonal]
  rfl

/-! transpose invariance -/

end X5AF
end X5mod_AF_Bounds

section X5mod_AF_Cond
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5AF
open X5QC
set_option linter.unusedSectionVars false

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

end X5AF
end X5mod_AF_Cond

section X5mod_AF_Mix2
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5AF
open X5QC
set_option linter.unusedSectionVars false

variable {A B X : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype X] [DecidableEq X]

end X5AF
end X5mod_AF_Mix2

section X5mod_QK_Vec
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QK
set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

end X5QK
end X5mod_QK_Vec

section X5mod_QK_Ops
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QK
set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

end X5QK
end X5mod_QK_Ops

section X5mod_QK_Pure
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QK
set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

end X5QK
end X5mod_QK_Pure

section X5mod_QK_Main
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QK
set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

end X5QK
end X5mod_QK_Main

section X5mod_AF_Main
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5AF
open X5QC
set_option linter.unusedSectionVars false

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

end X5AF
end X5mod_AF_Main

section X5mod_AF_Fannes

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms

namespace X5AF

end X5AF
end X5mod_AF_Fannes

section X5mod_AF_Reindex
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5AF
open X5QC
set_option linter.unusedSectionVars false

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

lemma trace_sub_equiv (e : n ≃ m) (X : Matrix m m ℂ) : (X.submatrix e e).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun j => X j j)

lemma aeval_sub_equiv (e : n ≃ m) (X : Matrix m m ℂ) (p : ℝ[X]) :
    aeval (X.submatrix e e) p = (aeval X p).submatrix e e := by
  have h := Polynomial.aeval_algHom_apply (Matrix.reindexAlgEquiv ℝ ℂ e.symm) X p
  simpa [Matrix.reindexAlgEquiv, Matrix.reindex_apply] using h

end X5AF
end X5mod_AF_Reindex

section X5mod_PK_Base
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- cfc of a Hermitian matrix is the aeval of any interpolating polynomial on a superset
of its spectrum. -/
lemma cfc_eq_interp {Y : Matrix n n ℂ} (hY : Y.IsHermitian) (S : Finset ℝ)
    (hS : spectrum ℝ Y ⊆ S) (f : ℝ → ℝ) :
    cfc f Y = aeval Y (Lagrange.interpolate S (fun x : ℝ => x) f) := by
  set p := Lagrange.interpolate S (fun x : ℝ => x) f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  rw [← cfc_polynomial p Y hY.isSelfAdjoint]
  exact cfc_congr fun x hx => (hp x (hS hx)).symm

lemma spec_fin (Y : Matrix n n ℂ) : spectrum ℝ Y ⊆ (Y.finite_real_spectrum).toFinset := by
  intro x hx; simpa using hx

/-- Transfer of cfc along any map that intertwines polynomial evaluation. -/
lemma cfc_transfer {X : Matrix m m ℂ} {Y : Matrix n n ℂ} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) (G : Matrix m m ℂ → Matrix n n ℂ)
    (hG : ∀ p : ℝ[X], aeval Y p = G (aeval X p)) (f : ℝ → ℝ) :
    cfc f Y = G (cfc f X) := by
  set S := (X.finite_real_spectrum).toFinset ∪ (Y.finite_real_spectrum).toFinset
  rw [cfc_eq_interp hY S ((spec_fin Y).trans subset_union_right),
    cfc_eq_interp hX S ((spec_fin X).trans subset_union_left), hG]

lemma cfc_sub_equiv {X : Matrix m m ℂ} (hX : X.IsHermitian) (e : n ≃ m) (f : ℝ → ℝ) :
    cfc f (X.submatrix e e) = (cfc f X).submatrix e e :=
  cfc_transfer hX (hX.submatrix e) (fun Z => Z.submatrix e e)
    (fun p => X5AF.aeval_sub_equiv e X p) f

/-! ### relative entropy -/

/-- universe-polymorphic copy of `SimpleSSA.Monotone.relEntropy` -/
noncomputable def relEntropy (ρ σ : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (ρ * cfc Real.log ρ - ρ * cfc Real.log σ)).re

lemma relEnt_def (ρ σ : Matrix n n ℂ) :
    relEntropy ρ σ = (Matrix.trace (ρ * cfc Real.log ρ - ρ * cfc Real.log σ)).re := rfl

lemma relEnt_eq {A : Type} [Fintype A] [DecidableEq A] (ρ σ : Matrix A A ℂ) :
    SimpleSSA.Monotone.relEntropy ρ σ = relEntropy ρ σ := rfl

lemma relEnt_sub {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (e : n ≃ m) :
    relEntropy (ρ.submatrix e e) (σ.submatrix e e) = relEntropy ρ σ := by
  rw [relEnt_def, relEnt_def, cfc_sub_equiv hρ, cfc_sub_equiv hσ, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv]
  have h2 : ∀ A B : Matrix m m ℂ, A.submatrix e e - B.submatrix e e = (A - B).submatrix e e :=
    fun A B => by ext; simp
  rw [h2, X5AF.trace_sub_equiv]

/-! ### full pinching via random signs -/

end X5PK
end X5mod_PK_Base

section X5mod_PK_Pinsker
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### classical part -/

/-! ### quantum part -/

end X5PK
end X5mod_PK_Pinsker

section X5mod_PK_Supp
open Matrix Finset Polynomial Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma aff_eq {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (a b : ℝ) :
    ((a : ℝ) : ℂ) • X + ((b : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) = cfc (fun x : ℝ => a * x + b) X := by
  rw [cfc_add (a := X) (fun x : ℝ => a * x) (fun _ => b), cfc_const_mul a (fun x : ℝ => x) X,
    cfc_id' ℝ X hX.isSelfAdjoint, cfc_const b X hX.isSelfAdjoint, Algebra.algebraMap_eq_smul_one,
    real_smul, real_smul]

lemma cfc_aff {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (a b : ℝ) (f : ℝ → ℝ) :
    cfc f (((a : ℝ) : ℂ) • X + ((b : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) =
      cfc (fun x => f (a * x + b)) X := by
  rw [aff_eq hX a b, ← cfc_comp f (fun x : ℝ => a * x + b) X hX.isSelfAdjoint
    ((X.finite_real_spectrum.image _).continuousOn f)]
  rfl

lemma aff_herm {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (a b : ℝ) :
    (((a : ℝ) : ℂ) • X + ((b : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian := by
  rw [aff_eq hX]; exact (cfc_predicate (R := ℝ) (fun x : ℝ => a * x + b) X : IsSelfAdjoint _)

/-- the trace term `Re Tr (X log Y)` in the eigenbasis of `Y` -/
lemma tr_mul_cfc {X Y : Matrix ι ι ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) (f : ℝ → ℝ) :
    (X * cfc f Y).trace.re =
      ∑ j, ((star (hY.eigenvectorUnitary : Matrix ι ι ℂ) * X * hY.eigenvectorUnitary) j j).re *
        f (hY.eigenvalues j) := by
  rw [hY.cfc_eq]
  unfold IsHermitian.cfc
  simp only [Unitary.conjStarAlgAut_apply]
  set U := (hY.eigenvectorUnitary : Matrix ι ι ℂ)
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, ← Matrix.mul_assoc]
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_diagonal, Complex.mul_re]


end X5PK
end X5mod_PK_Supp

section X5mod_PK_Coh
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

end X5PK
end X5mod_PK_Coh

section X5mod_PK_Pin
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

open QAlgorithms.Papers.Independent.Dependency50.P35

variable {I : Type} [Fintype I] [DecidableEq I]

end X5PK
end X5mod_PK_Pin

section X5mod_PK_CohMain
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma ker_single {δ : Matrix n n ℂ} {ρ : Matrix n n ℂ}
    (hker : LinearMap.ker δ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin) (hδ : ∀ i j, i ≠ j → δ i j = 0)
    (i : n) (hi : δ i i = 0) : ρ i i = 0 := by
  have hv : Pi.single i (1 : ℂ) ∈ LinearMap.ker δ.mulVecLin := by
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    ext k
    rw [Matrix.mulVec_single_one]
    by_cases h : k = i
    · subst h; simpa using hi
    · simpa using hδ k i h
  have := hker hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at this
  have h2 := congrFun this i
  rw [Matrix.mulVec_single_one] at h2
  simpa using h2

end X5PK
end X5mod_PK_CohMain

section X5mod_PK_PinMain
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

open QAlgorithms.Papers.Independent.Dependency50.P35

variable {I : Type} [Fintype I] [DecidableEq I]

end X5PK

namespace X5PK
open QAlgorithms.Papers.Independent.Dependency50.P35
variable {I : Type} [Fintype I] [DecidableEq I]

end X5PK
end X5mod_PK_PinMain

section X5mod_PK_CQ
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

variable {L H : Type*} [Fintype L] [DecidableEq L] [Fintype H] [DecidableEq H]

/-- block-diagonal matrix, block index first -/
def bd (X : L → Matrix H H ℂ) : Matrix (L × H) (L × H) ℂ :=
  fun a b => if a.1 = b.1 then X a.1 a.2 b.2 else 0

lemma bd_mul (X Y : L → Matrix H H ℂ) : bd X * bd Y = bd (fun k => X k * Y k) := by
  ext a b
  simp only [bd, Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases h : a.1 = b.1
  · rw [if_pos h, Finset.sum_eq_single a.1]
    · simp [h]
    · intro k _ hk; simp [Ne.symm hk]
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases hk : a.1 = k
    · subst hk; simp [h]
    · simp [hk]

lemma bd_add (X Y : L → Matrix H H ℂ) : bd X + bd Y = bd (fun k => X k + Y k) := by
  ext a b; simp only [bd, Matrix.add_apply]; split_ifs <;> simp

lemma bd_smul (c : ℝ) (X : L → Matrix H H ℂ) : c • bd X = bd (fun k => c • X k) := by
  ext a b; simp only [bd, Matrix.smul_apply]; split_ifs <;> simp

lemma bd_one : bd (fun _ : L => (1 : Matrix H H ℂ)) = 1 := by
  ext a b
  simp only [bd, Matrix.one_apply, Prod.ext_iff]
  by_cases h : a.1 = b.1 <;> simp [h]

lemma bd_pow (X : L → Matrix H H ℂ) (k : ℕ) : bd X ^ k = bd (fun l => X l ^ k) := by
  induction k with
  | zero => simp [bd_one]
  | succ k ih => rw [pow_succ, ih, bd_mul]; simp [pow_succ]

lemma bd_ct (X : L → Matrix H H ℂ) : (bd X)ᴴ = bd (fun k => (X k)ᴴ) := by
  ext a b
  simp only [bd, conjTranspose_apply]
  by_cases h : a.1 = b.1
  · rw [if_pos h.symm, if_pos h, h]
  · rw [if_neg (Ne.symm h), if_neg h]; simp

lemma bd_trace (X : L → Matrix H H ℂ) : (bd X).trace = ∑ k, (X k).trace := by
  simp [Matrix.trace, bd, Fintype.sum_prod_type]

lemma aeval_bd (X : L → Matrix H H ℂ) (p : ℝ[X]) :
    aeval (bd X) p = bd (fun k => aeval (X k) p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, bd_add]
  | monomial k a =>
    simp only [aeval_monomial, bd_pow, ← Algebra.smul_def, bd_smul]

lemma bd_herm {X : L → Matrix H H ℂ} (hX : ∀ k, (X k).IsHermitian) : (bd X).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [bd_ct]; congr 1; ext k : 1; exact (hX k).eq

lemma cfc_bd {X : L → Matrix H H ℂ} (hX : ∀ k, (X k).IsHermitian) (f : ℝ → ℝ) :
    cfc f (bd X) = bd (fun k => cfc f (X k)) := by
  set S := ((bd X).finite_real_spectrum).toFinset ∪
    Finset.univ.biUnion (fun k => ((X k).finite_real_spectrum).toFinset)
  rw [cfc_eq_interp (bd_herm hX) S ((spec_fin _).trans subset_union_left), aeval_bd]
  congr 1; ext k : 1
  rw [cfc_eq_interp (hX k) S ((spec_fin _).trans (fun x hx => subset_union_right
    (Finset.mem_biUnion.2 ⟨k, mem_univ k, hx⟩)))]

open QAlgorithms.Papers.Independent.Dependency50.P24

end X5PK

namespace X5PK
open QAlgorithms.Papers.Independent.Dependency50.P24
variable {L H : Type*} [Fintype L] [DecidableEq L] [Fintype H] [DecidableEq H]

end X5PK
end X5mod_PK_CQ

section X5mod_PK_Twist
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma ker_conj' {V M N : Matrix ι ι ℂ} (hV : Vᴴ * V = 1)
    (h : LinearMap.ker M.mulVecLin ≤ LinearMap.ker N.mulVecLin) :
    LinearMap.ker (V * M * Vᴴ).mulVecLin ≤ LinearMap.ker (V * N * Vᴴ).mulVecLin := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  have h1 : M *ᵥ (Vᴴ *ᵥ v) = 0 := by
    have := congrArg (fun x => Vᴴ *ᵥ x) hv
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero, ← Matrix.mul_assoc, hV,
      Matrix.one_mul] at this
    simpa [Matrix.mulVec_mulVec] using this
  have h2 := h (show Vᴴ *ᵥ v ∈ LinearMap.ker M.mulVecLin by simpa using h1)
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h2
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero]

end X5PK

namespace X5PK
variable {J H : Type*} [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]

end X5PK
end X5mod_PK_Twist

section X5mod_PK_Pk2
open Matrix Finset Polynomial Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

end X5PK
end X5mod_PK_Pk2

section X5mod_PK_Cop
open Matrix Finset Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
set_option linter.unusedSectionVars false
open QAlgorithms.Papers.Independent.Information100.P60 (copies)

variable {I : Type*} [Fintype I] [DecidableEq I]

end X5PK

namespace X5PK
open QAlgorithms.Papers.Independent.Information100.P60 (copies)
open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy IsSupported)

end X5PK
end X5mod_PK_Cop

section X5mod_PK_Mean
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
open QAlgorithms.Papers.Independent.Dependency50.P24
set_option linter.unusedSectionVars false

variable {L H : Type*} [Fintype L] [DecidableEq L] [Fintype H] [DecidableEq H]

lemma bd_psd {X : L → Matrix H H ℂ} (h : ∀ k, (X k).PosSemidef) : (bd X).PosSemidef := by
  have : ∀ k, ∃ B : Matrix H H ℂ, X k = star B * B := fun k =>
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (h k).nonneg
  choose B hB using this
  have e : bd X = (bd B)ᴴ * bd B := by
    rw [bd_ct, bd_mul]; congr 1; ext k : 1; rw [hB k]; rfl
  rw [e]; exact posSemidef_conjTranspose_mul_self _

end X5PK
end X5mod_PK_Mean

section X5mod_PK_Add
open Matrix Finset Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

section
variable {L H : Type*} [Fintype L] [DecidableEq L] [Fintype H] [DecidableEq H]

lemma bd_sub (X Y : L → Matrix H H ℂ) : bd X - bd Y = bd (fun k => X k - Y k) := by
  ext a b; simp only [bd, Matrix.sub_apply]; split_ifs <;> simp

lemma relEnt_bd {X Y : L → Matrix H H ℂ} (hX : ∀ k, (X k).IsHermitian)
    (hY : ∀ k, (Y k).IsHermitian) :
    relEntropy (bd X) (bd Y) = ∑ k, relEntropy (X k) (Y k) := by
  rw [relEnt_def, cfc_bd hX, cfc_bd hY, bd_mul, bd_mul, bd_sub, bd_trace, Complex.re_sum]
  rfl

/-- `relEnt (s X) (t Y)` for positive definite `X, Y` -/
lemma relEnt_smul {X Y : Matrix H H ℂ} (hX : X.PosDef) (hY : Y.PosDef) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) :
    relEntropy (s • X) (t • Y) =
      s * relEntropy X Y + s * X.trace.re * (Real.log s - Real.log t) := by
  have lg : ∀ {Z : Matrix H H ℂ}, Z.PosDef → ∀ {r : ℝ}, 0 < r →
      cfc Real.log (r • Z) = algebraMap ℝ _ (Real.log r) + cfc Real.log Z := by
    intro Z hZ r hr
    have e1 : r • Z = ((r : ℝ) : ℂ) • Z + ((0 : ℝ) : ℂ) • (1 : Matrix H H ℂ) := by
      simp
    rw [e1, cfc_aff hZ.isHermitian, ← cfc_const_add (Real.log r) Real.log Z
      (hf := Z.finite_real_spectrum.continuousOn _)]
    refine cfc_congr fun x hx => ?_
    obtain ⟨i, rfl⟩ := hZ.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
    simp only [add_zero]
    exact Real.log_mul hr.ne' (hZ.eigenvalues_pos i).ne'
  rw [relEnt_def, relEnt_def, lg hX hs, lg hY ht]
  simp only [Algebra.algebraMap_eq_smul_one, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Complex.sub_re,
    Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring
end

variable {H : Type} [Fintype H] [DecidableEq H]

/-- flag state, flag (`Bool`) on the right -/
noncomputable def flg (X Y : Matrix H H ℂ) : Matrix (H × Bool) (H × Bool) ℂ :=
  (bd (fun b : Bool => if b then X else Y)).submatrix (Equiv.prodComm H Bool) (Equiv.prodComm H Bool)

lemma flg_ptr (X Y : Matrix H H ℂ) : WildeQIT.partialTraceRight (flg X Y) = X + Y := by
  ext i j
  simp [WildeQIT.partialTraceRight, flg, bd, add_comm]

lemma flg_trace (X Y : Matrix H H ℂ) : (flg X Y).trace = X.trace + Y.trace := by
  rw [flg, X5AF.trace_sub_equiv, bd_trace]; simp [add_comm]

lemma flg_relEnt {X Y Z W : Matrix H H ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hZ : Z.IsHermitian) (hW : W.IsHermitian) :
    relEntropy (flg X Y) (flg Z W) = relEntropy X Z + relEntropy Y W := by
  have h1 : ∀ b : Bool, (if b then X else Y).IsHermitian := fun b => by cases b <;> simpa
  have h2 : ∀ b : Bool, (if b then Z else W).IsHermitian := fun b => by cases b <;> simpa
  rw [flg, flg, relEnt_sub (bd_herm h1) (bd_herm h2), relEnt_bd h1 h2]
  simp [add_comm]

lemma flg_psd {X Y : Matrix H H ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (flg X Y).PosSemidef :=
  (bd_psd (fun b => by cases b <;> simpa)).submatrix _

lemma flg_posDef {X Y : Matrix H H ℂ} (hX : X.PosDef) (hY : Y.PosDef) : (flg X Y).PosDef := by
  refine (flg_psd hX.posSemidef hY.posSemidef).posDef_iff_isUnit.2
    ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse (B := flg X⁻¹ Y⁻¹) ?_))
  rw [flg, flg, Matrix.submatrix_mul_equiv, bd_mul]
  have : (fun k : Bool => (if k then X else Y) * (if k then X⁻¹ else Y⁻¹)) = fun _ => 1 := by
    ext k : 1
    cases k
    · exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hY.isUnit)
    · exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hX.isUnit)
  rw [this, bd_one]
  exact Matrix.submatrix_one_equiv _

lemma ptr_smul {a b : Type} [Fintype b] (r : ℝ) (M : Matrix (a × b) (a × b) ℂ) :
    WildeQIT.partialTraceRight (r • M) = r • WildeQIT.partialTraceRight M := by
  ext i j; simp [WildeQIT.partialTraceRight, Finset.smul_sum]

lemma tr_re {n : Type*} [Fintype n] {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    M.trace = ((M.trace.re : ℝ) : ℂ) := by
  have := (Complex.nonneg_iff.1 hM.trace_nonneg).2
  exact Complex.ext (by simp) (by simp [← this])

/-- joint subadditivity for positive definite arguments -/
lemma joint [Nonempty H] {A B C D : Matrix H H ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hC : C.PosDef) (hD : D.PosDef) :
    relEntropy (A + C) (B + D) ≤ relEntropy A B + relEntropy C D := by
  have hω := flg_posDef hA hC
  have hτ := flg_posDef hB hD
  set ω := flg A C
  set τ := flg B D
  have pos : ∀ {M : Matrix (H × Bool) (H × Bool) ℂ}, M.PosDef → 0 < M.trace.re := fun hM => by
    have h := hM.trace_pos
    exact (Complex.lt_def.1 h).1
  have dens : ∀ {M : Matrix (H × Bool) (H × Bool) ℂ}, M.PosDef →
      QAlgorithms.IsDensityMatrix ((M.trace.re)⁻¹ • M) ∧ ((M.trace.re)⁻¹ • M).PosDef := by
    intro M hM
    have hp := pos hM
    have hpd : ((M.trace.re)⁻¹ • M).PosDef := hM.smul (inv_pos.2 hp)
    refine ⟨⟨hpd.posSemidef, ?_⟩, hpd⟩
    rw [Matrix.trace_smul, tr_re hM.posSemidef]
    apply Complex.ext <;> simp [hp.ne']
  obtain ⟨d1, d2⟩ := dens hω
  obtain ⟨d3, d4⟩ := dens hτ
  have h := SimpleSSA.Monotone.eq_4 _ _ d1 d2 d3 d4
  rw [relEnt_eq, relEnt_eq, ptr_smul, ptr_smul, flg_ptr, flg_ptr,
    relEnt_smul (hA.add hC) (hB.add hD) (inv_pos.2 (pos hω)) (inv_pos.2 (pos hτ)),
    relEnt_smul hω hτ (inv_pos.2 (pos hω)) (inv_pos.2 (pos hτ)),
    flg_relEnt hA.isHermitian hC.isHermitian hB.isHermitian hD.isHermitian] at h
  have e : (A + C).trace.re = ω.trace.re := by rw [flg_trace, Matrix.trace_add]
  rw [e] at h
  have := inv_pos.2 (pos hω)
  nlinarith

/-- `X + ε` -/
noncomputable def pe (ε : ℝ) (X : Matrix H H ℂ) : Matrix H H ℂ :=
  ((1 : ℝ) : ℂ) • X + ((ε : ℝ) : ℂ) • (1 : Matrix H H ℂ)

lemma pe_posDef {X : Matrix H H ℂ} (hX : X.PosSemidef) {ε : ℝ} (hε : 0 < ε) : (pe ε X).PosDef :=
  Matrix.PosDef.posSemidef_add (by simpa using hX)
    ((Matrix.PosDef.one (n := H) (R := ℂ)).smul (a := ((ε : ℝ) : ℂ)) (by exact_mod_cast hε))

lemma pe_add (X Y : Matrix H H ℂ) (ε : ℝ) : pe ε X + pe ε Y = pe (2 * ε) (X + Y) := by
  unfold pe; simp only [Complex.ofReal_one, one_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [mul_smul]; module

lemma relEnt_self (X : Matrix H H ℂ) : relEntropy X X = 0 := by
  simp [relEnt_def]

lemma ker_add {A B C : Matrix H H ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef)
    (hker : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) :
    LinearMap.ker (B + C).mulVecLin ≤ LinearMap.ker (A + C).mulVecLin := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  have h0 : star v ⬝ᵥ B *ᵥ v + star v ⬝ᵥ C *ᵥ v = 0 := by
    rw [← dotProduct_add, ← Matrix.add_mulVec, hv, dotProduct_zero]
  have n1 := hB.dotProduct_mulVec_nonneg v
  have n2 := hC.dotProduct_mulVec_nonneg v
  have z1 : star v ⬝ᵥ B *ᵥ v = 0 := le_antisymm (by rw [← h0]; exact le_add_of_nonneg_right n2) n1
  have z2 : star v ⬝ᵥ C *ᵥ v = 0 := by rw [z1, zero_add] at h0; exact h0
  have hBv := (hB.dotProduct_mulVec_zero_iff v).1 z1
  have hCv := (hC.dotProduct_mulVec_zero_iff v).1 z2
  have hAv : A *ᵥ v = 0 := by
    have := hker (show v ∈ LinearMap.ker B.mulVecLin by simpa using hBv)
    simpa using this
  rw [Matrix.add_mulVec, hAv, hCv, add_zero]

/-- continuity of `ε ↦ D(X + cε ‖ Y + cε)` at `0` under the support condition -/
theorem cont {X Y : Matrix H H ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hker : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin) (c : ℝ) :
    Tendsto (fun ε => relEntropy (pe (c * ε) X) (pe (c * ε) Y)) (𝓝 0) (𝓝 (relEntropy X Y)) := by
  have hρH := hX.isHermitian
  have hσH := hY.isHermitian
  set U := (hσH.eigenvectorUnitary : Matrix H H ℂ)
  set s := hσH.eigenvalues
  set l := hρH.eigenvalues
  set r : H → ℝ := fun j => ((star U * X * U) j j).re
  let F : ℝ → ℝ := fun ε =>
    (∑ i, (1 * l i + ε) * Real.log (1 * l i + ε)) -
      ∑ j, (1 * r j + ε) * Real.log (1 * s j + ε)
  have hA : ∀ ε : ℝ, relEntropy (pe ε X) (pe ε Y) = F ε := by
    intro ε
    have h1 := aff_herm hρH 1 ε
    rw [relEnt_def, Matrix.trace_sub, Complex.sub_re]
    unfold pe
    rw [mul_log _ h1, cfc_aff hρH, cfc_aff hσH, X5AF.tr_cfc hρH, Complex.re_sum,
      tr_mul_cfc h1 hσH]
    simp only [Complex.ofReal_re]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Unitary.star_mul_self_of_mem hσH.eigenvectorUnitary.2]
    simp [r, Complex.mul_re]
    rfl
  have hsd : star U * Y * U = diagonal (fun j => ((s j : ℝ) : ℂ)) := by
    have hs := hσH.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at hs
    simp only [Unitary.coe_star, star_star] at hs
    exact hs
  have hs0 : ∀ j, 0 ≤ s j := fun j => hY.eigenvalues_nonneg j
  have hrs : ∀ j, s j = 0 → r j = 0 := fun j hj => by
    have hV : (Uᴴ)ᴴ * Uᴴ = 1 := by
      rw [conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose]
      exact Unitary.mul_star_self_of_mem hσH.eigenvectorUnitary.2
    have hk := ker_conj' hV hker
    rw [conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose, hsd] at hk
    have := ker_single hk (fun a b hab => by simp [hab]) j (by simp [hj])
    simp [r, this]
  have hB : ContinuousAt F 0 := by
    have c1 : ∀ i, ContinuousAt (fun ε : ℝ => (1 * l i + ε) *
        Real.log (1 * l i + ε)) 0 := fun i =>
      (Real.continuous_mul_log.comp (by fun_prop : Continuous fun ε : ℝ =>
        1 * l i + ε)).continuousAt
    have c2 : ∀ j, ContinuousAt (fun ε : ℝ => (1 * r j + ε) *
        Real.log (1 * s j + ε)) 0 := fun j => by
      rcases (hs0 j).eq_or_lt with h | h
      · have hr := hrs j h.symm
        rw [hr, ← h]
        simp only [mul_zero, zero_add]
        exact Real.continuous_mul_log.continuousAt
      · refine ContinuousAt.mul (by fun_prop) (ContinuousAt.log (by fun_prop) ?_)
        simp; exact h.ne'
    exact (tendsto_finsetSum _ (fun i _ => c1 i)).sub (tendsto_finsetSum _ (fun j _ => c2 j))
  have hD : F 0 = relEntropy X Y := by
    rw [← hA 0]; unfold pe; simp
  have hc : Tendsto (fun ε : ℝ => c * ε) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_const_mul c).tendsto 0
  have := hB.tendsto.comp hc
  rw [hD] at this
  refine this.congr fun ε => ?_
  simp only [Function.comp, hA]

/-- `D(A + C ‖ B + C) ≤ D(A ‖ B)` for PSD `A, B, C` with `ker B ⊆ ker A` -/
theorem add_core [Nonempty H] {A B C : Matrix H H ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hC : C.PosSemidef) (hker : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) :
    relEntropy (A + C) (B + C) ≤ relEntropy A B := by
  have t1 := cont (hA.add hC) (hB.add hC) (ker_add hA hB hC hker) 2
  have t2 := cont hA hB hker 1
  refine le_of_tendsto_of_tendsto (t1.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0)))
    (t2.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))) ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have h := joint (pe_posDef hA hε) (pe_posDef hB hε) (pe_posDef hC hε) (pe_posDef hC hε)
  rw [pe_add, pe_add, relEnt_self, add_zero] at h
  simpa using h

end X5PK
end X5mod_PK_Add

open Matrix
open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy IsSupported)
open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

theorem solution {d : ℕ} (hd : 0 < d) (A B C : Mat d)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef) :
    relativeEntropy (A + C) (B + C) ≤ relativeEntropy A B := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  by_cases hs : IsSupported A B
  · have hs' : IsSupported (A + C) (B + C) := X5PK.ker_add hA hB hC hs
    have e : ∀ {X Y : Mat d}, X.IsHermitian →
        (cfc (fun x : ℝ => x * Real.log x) X - X * cfc Real.log Y).trace.re =
          X5PK.relEntropy X Y := fun hX => by
      rw [X5PK.relEnt_def, X5QC.mul_log _ hX]
    simp only [relativeEntropy, if_pos hs, if_pos hs', e hA.isHermitian,
      e (hA.add hC).isHermitian, EReal.coe_le_coe_iff]
    exact X5PK.add_core hA hB hC hs
  · simp [relativeEntropy, if_neg hs]
