-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P54.local_pinching_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T10:00:57.397962+00:00
-- url     : https://prove2.me/submissions/77d2926e-b12e-47c1-a959-81f5eb4b4ce5

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_backgroundSSA
import Theorems.Thm_QAlgorithms_Arunachalam_vnEntropy_subadditive
import Theorems.Thm_SimpleSSA_Monotone_eq_4
import Theorems.Thm_BanditAlgorithm_bernoulli_relative_entropy_pinsker
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54

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

lemma sqrt_herm (X : Matrix I I ℂ) : (cfc Real.sqrt X)ᴴ = cfc Real.sqrt X :=
  (cfc_predicate Real.sqrt X : IsSelfAdjoint _)

lemma sqrt_sq {X : Matrix I I ℂ} (hX : X.PosSemidef) : cfc Real.sqrt X * cfc Real.sqrt X = X := by
  have hs : IsSelfAdjoint X := hX.1.isSelfAdjoint
  rw [← cfc_mul _ _ _ (fin _ _) (fin _ _)]
  conv_rhs => rw [← cfc_id' ℝ X hs]
  refine cfc_congr fun x hx => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hX.nonneg hx)

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

lemma tr_pow_swap (X : Matrix m n ℂ) (k : ℕ) :
    ((Xᴴ * X) ^ (k + 1)).trace = ((X * Xᴴ) ^ (k + 1)).trace := by
  have h : ∀ k : ℕ, (Xᴴ * X) ^ (k + 1) = Xᴴ * (X * Xᴴ) ^ k * X := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
  rw [h, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← pow_succ']

lemma tr_aeval_swap (X : Matrix m n ℂ) (p : ℝ[X]) (hp : p.coeff 0 = 0) :
    (aeval (Xᴴ * X) p).trace = (aeval (X * Xᴴ) p).trace := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rcases i with _ | k
  · simp [hp]
  · rw [tr_pow_swap]

theorem tr_cfc_swap (X : Matrix m n ℂ) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f (Xᴴ * X)).trace = (cfc f (X * Xᴴ)).trace := by
  set A := Xᴴ * X
  set B := X * Xᴴ
  have hA : IsSelfAdjoint A := (Matrix.posSemidef_conjTranspose_mul_self X).1.isSelfAdjoint
  have hB : IsSelfAdjoint B := (Matrix.posSemidef_self_mul_conjTranspose X).1.isSelfAdjoint
  have fA : (spectrum ℝ A).Finite := A.finite_real_spectrum
  have fB : (spectrum ℝ B).Finite := B.finite_real_spectrum
  set s : Finset ℝ := {0} ∪ fA.toFinset ∪ fB.toFinset
  set p := Lagrange.interpolate s (fun x : ℝ => x) f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  have h1 : cfc f A = cfc (fun x => p.eval x) A :=
    cfc_congr fun x hx => (hp x (by simp [s, fA.mem_toFinset.2 hx])).symm
  have h2 : cfc f B = cfc (fun x => p.eval x) B :=
    cfc_congr fun x hx => (hp x (by simp [s, fB.mem_toFinset.2 hx])).symm
  rw [h1, h2, cfc_polynomial p A hA, cfc_polynomial p B hB]
  refine tr_aeval_swap X p ?_
  rw [Polynomial.coeff_zero_eq_eval_zero, hp 0 (by simp [s]), hf]

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

lemma aeval_diag (δ : ι → ℂ) (p : ℝ[X]) :
    aeval (diagonal δ) p = diagonal (fun k => aeval (δ k) p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, diagonal_add]
  | monomial k c =>
    simp only [aeval_monomial, Matrix.algebraMap_eq_diagonal, diagonal_pow, diagonal_mul_diagonal]
    rfl

lemma cfc_diag (d : ι → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun k => ((d k : ℝ) : ℂ))) = diagonal (fun k => ((f (d k) : ℝ) : ℂ)) := by
  set D := diagonal (fun k => ((d k : ℝ) : ℂ))
  have hfin : (spectrum ℝ D).Finite := D.finite_real_spectrum
  set s : Finset ℝ := Finset.univ.image d ∪ hfin.toFinset
  set p := Lagrange.interpolate s (fun x : ℝ => x) f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  have hD : IsSelfAdjoint D := by
    rw [← Matrix.isHermitian_iff_isSelfAdjoint]
    exact isHermitian_diagonal_of_self_adjoint _ (by ext k; simp [Complex.conj_ofReal])
  have h1 : cfc f D = cfc (fun x => p.eval x) D :=
    cfc_congr fun x hx => (hp x (Finset.mem_union_right _ (hfin.mem_toFinset.2 hx))).symm
  rw [h1, cfc_polynomial p D hD, aeval_diag]
  congr 1; ext k
  rw [show ((d k : ℝ) : ℂ) = algebraMap ℝ ℂ (d k) from rfl, aeval_algebraMap_apply,
    Polynomial.aeval_def, Algebra.algebraMap_self, ← Polynomial.eval,
    hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))]
  rfl

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

lemma OEmb.herm (hE : OEmb E) {Y : K → Matrix m m ℂ} (hY : ∀ b, (Y b).IsHermitian) :
    (∑ b, E b (Y b)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hE.star, (hY b).eq]

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

/-- `Tr (X log X)`, in nats. -/
noncomputable def T (X : Matrix ι ι ℂ) : ℝ := (cfc (fun x : ℝ => x * Real.log x) X).trace.re

lemma vn_eq (X : Matrix ι ι ℂ) : QAlgorithms.vnEntropy X = -T X / Real.log 2 := by
  unfold QAlgorithms.vnEntropy T
  have : cfc (fun x : ℝ => x * Real.logb 2 x) X =
      ((Real.log 2)⁻¹ : ℝ) • cfc (fun x : ℝ => x * Real.log x) X := by
    rw [← cfc_smul _ _ _ (X5B2.fin _ _)]
    refine cfc_congr fun x _ => ?_
    simp only [smul_eq_mul, Real.logb]; ring
  rw [this, Matrix.trace_smul]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  ring

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

lemma tr_traceLeft (X : Matrix (ι × κ) (ι × κ) ℂ) : (QAlgorithms.traceLeft X).trace = X.trace := by
  simp [Matrix.trace, QAlgorithms.traceLeft, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

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

lemma tr_aeval_transpose (X : Matrix ι ι ℂ) (p : ℝ[X]) :
    (aeval Xᵀ p).trace = (aeval X p).trace := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul, Matrix.trace_smul, ← Matrix.transpose_pow, Matrix.trace_transpose]

lemma tr_cfc_transpose {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    (cfc f Xᵀ).trace = (cfc f X).trace := by
  have hA : IsSelfAdjoint Xᵀ := hX.transpose.isSelfAdjoint
  have hB : IsSelfAdjoint X := hX.isSelfAdjoint
  have fA : (spectrum ℝ Xᵀ).Finite := Xᵀ.finite_real_spectrum
  have fB : (spectrum ℝ X).Finite := X.finite_real_spectrum
  set s : Finset ℝ := fA.toFinset ∪ fB.toFinset
  set p := Lagrange.interpolate s (fun x : ℝ => x) f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  have h1 : cfc f Xᵀ = cfc (fun x => p.eval x) Xᵀ :=
    cfc_congr fun x hx => (hp x (by simp [s, fA.mem_toFinset.2 hx])).symm
  have h2 : cfc f X = cfc (fun x => p.eval x) X :=
    cfc_congr fun x hx => (hp x (by simp [s, fB.mem_toFinset.2 hx])).symm
  rw [h1, h2, cfc_polynomial p _ hA, cfc_polynomial p X hB]
  exact tr_aeval_transpose X p

lemma T_transpose {X : Matrix ι ι ℂ} (hX : X.IsHermitian) : T Xᵀ = T X := by
  unfold T; rw [tr_cfc_transpose hX]

lemma T_swap {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) : T (Mᴴ * M) = T (M * Mᴴ) := by
  unfold T; rw [X5UH.tr_cfc_swap M _ (by simp)]

end X5AF
end X5mod_AF_Bounds

section X5mod_AF_Cond
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5AF
open X5QC
set_option linter.unusedSectionVars false

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- the matrix of the canonical purification, regrouped as `B | A R` -/
noncomputable def Mp (rho : Matrix (A × B) (A × B) ℂ) : Matrix B (A × (A × B)) ℂ :=
  fun b ar => cfc Real.sqrt rho (ar.1, b) ar.2

lemma Mp_mul {rho : Matrix (A × B) (A × B) ℂ} (h : rho.PosSemidef) :
    Mp rho * (Mp rho)ᴴ = QAlgorithms.traceLeft rho := by
  conv_rhs => rw [← X5B2.sqrt_sq h]
  conv_rhs => enter [1, 2]; rw [← X5B2.sqrt_herm rho]
  ext b b'
  simp [Mp, Matrix.mul_apply, QAlgorithms.traceLeft, Fintype.sum_prod_type]

lemma tau_trR {rho : Matrix (A × B) (A × B) ℂ} (h : rho.PosSemidef) :
    QAlgorithms.traceRight ((Mp rho)ᴴ * Mp rho)ᵀ = QAlgorithms.traceRight rho := by
  conv_rhs => rw [← X5B2.sqrt_sq h]
  conv_rhs => enter [1, 2]; rw [← X5B2.sqrt_herm rho]
  ext a a'
  simp only [QAlgorithms.traceRight, Matrix.transpose_apply, Matrix.mul_apply, Mp,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.of_apply]
  refine (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun y _ => ?_
  simp [mul_comm]

lemma tau_trL {rho : Matrix (A × B) (A × B) ℂ} (h : rho.PosSemidef) :
    QAlgorithms.traceLeft ((Mp rho)ᴴ * Mp rho)ᵀ = rhoᵀ := by
  conv_rhs => rw [← X5B2.sqrt_sq h]
  conv_rhs => enter [1, 1]; rw [← X5B2.sqrt_herm rho]
  ext r r'
  simp only [QAlgorithms.traceLeft, Matrix.transpose_apply, Matrix.mul_apply, Mp,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.of_apply]

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

lemma cfc_conj (U : unitary (Matrix n n ℂ)) {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (f : ℝ → ℝ) :
    cfc f ((U : Matrix n n ℂ) * X * star (U : Matrix n n ℂ)) =
      (U : Matrix n n ℂ) * cfc f X * star (U : Matrix n n ℂ) := by
  have hY : ((U : Matrix n n ℂ) * X * star (U : Matrix n n ℂ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.star_eq_conjTranspose, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, hX.eq, Matrix.mul_assoc]
  refine cfc_transfer hX hY (fun Z => (U : Matrix n n ℂ) * Z * star (U : Matrix n n ℂ))
    (fun p => ?_) f
  have h := Polynomial.aeval_algHom_apply
    ((Unitary.conjStarAlgAut ℝ (Matrix n n ℂ) U).toAlgEquiv.toAlgHom) X p
  simpa using h

lemma cfc_sub_equiv {X : Matrix m m ℂ} (hX : X.IsHermitian) (e : n ≃ m) (f : ℝ → ℝ) :
    cfc f (X.submatrix e e) = (cfc f X).submatrix e e :=
  cfc_transfer hX (hX.submatrix e) (fun Z => Z.submatrix e e)
    (fun p => X5AF.aeval_sub_equiv e X p) f

lemma aeval_diag (d : n → ℝ) (p : ℝ[X]) :
    aeval (diagonal (fun i => ((d i : ℝ) : ℂ))) p =
      diagonal (fun i => ((p.eval (d i) : ℝ) : ℂ)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, diagonal_add]
  | monomial k a =>
    simp only [aeval_monomial, diagonal_pow, eval_monomial]
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_mul]
    ext i j
    by_cases h : i = j
    · subst h; simp [Complex.real_smul]
    · simp [h]

lemma diag_herm (d : n → ℝ) : (diagonal (fun i => ((d i : ℝ) : ℂ))).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [diagonal_conjTranspose]; congr 1; ext i; simp [Complex.conj_ofReal]

lemma cfc_diag (d : n → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun i => ((d i : ℝ) : ℂ))) = diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  set S := (Finset.univ.image d) ∪
    ((diagonal (fun i => ((d i : ℝ) : ℂ))).finite_real_spectrum).toFinset
  rw [cfc_eq_interp (diag_herm d) S ((spec_fin _).trans subset_union_right), aeval_diag]
  congr 1; ext i
  congr 2
  exact Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h)
    (subset_union_left (mem_image_of_mem d (mem_univ i)))

/-! ### relative entropy -/

/-- universe-polymorphic copy of `SimpleSSA.Monotone.relEntropy` -/
noncomputable def relEntropy (ρ σ : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (ρ * cfc Real.log ρ - ρ * cfc Real.log σ)).re

lemma relEnt_def (ρ σ : Matrix n n ℂ) :
    relEntropy ρ σ = (Matrix.trace (ρ * cfc Real.log ρ - ρ * cfc Real.log σ)).re := rfl

lemma relEnt_eq {A : Type} [Fintype A] [DecidableEq A] (ρ σ : Matrix A A ℂ) :
    SimpleSSA.Monotone.relEntropy ρ σ = relEntropy ρ σ := rfl

lemma relEnt_conj (U : unitary (Matrix n n ℂ)) {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (hσ : σ.IsHermitian) :
    relEntropy ((U : Matrix n n ℂ) * ρ * star (U : Matrix n n ℂ))
      ((U : Matrix n n ℂ) * σ * star (U : Matrix n n ℂ)) = relEntropy ρ σ := by
  rw [relEnt_def, relEnt_def, cfc_conj U hρ, cfc_conj U hσ]
  have hU : star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1 := Unitary.star_mul_self_of_mem U.2
  congr 1
  set V := (U : Matrix n n ℂ)
  have e : ∀ A B : Matrix n n ℂ, V * A * star V * (V * B * star V) = V * (A * B) * star V := by
    intro A B
    calc V * A * star V * (V * B * star V) = V * A * (star V * V) * B * star V := by
          simp only [Matrix.mul_assoc]
      _ = V * (A * B) * star V := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e, e]
  have h2 : ∀ A B : Matrix n n ℂ, V * A * star V - V * B * star V = V * (A - B) * star V := by
    intro A B; rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [h2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

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

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- flag state, flag (`Bool`) on the right -/
noncomputable def flg (X Y : Matrix H H ℂ) : Matrix (H × Bool) (H × Bool) ℂ :=
  (bd (fun b : Bool => if b then X else Y)).submatrix (Equiv.prodComm H Bool) (Equiv.prodComm H Bool)

lemma flg_ptr {H : Type} [Fintype H] [DecidableEq H] (X Y : Matrix H H ℂ) : WildeQIT.partialTraceRight (flg X Y) = X + Y := by
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
lemma joint {H : Type} [Fintype H] [DecidableEq H] [Nonempty H] {A B C D : Matrix H H ℂ} (hA : A.PosDef) (hB : B.PosDef)
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

end X5PK
end X5mod_PK_Add

section X5mod_PR_Main
open Matrix Finset Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PR
open X5QC X5PK
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section
variable {L H : Type*} [Fintype L] [DecidableEq L] [Fintype H] [DecidableEq H]

end

section priv
open QAlgorithms.Papers.Independent.Dependency50.P24
variable {d : ℕ} [NeZero d] {H : Type*} [Fintype H] [DecidableEq H]

lemma T_iso {m : Type*} [Fintype m] [DecidableEq m] {τ : Matrix H H ℂ} (hτ : τ.PosSemidef)
    (M : Matrix m H ℂ) (hM : Mᴴ * M = 1) : T (M * τ * Mᴴ) = T τ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hτ.nonneg
  rw [Matrix.star_eq_conjTranspose] at hB
  have e1 : M * τ * Mᴴ = (B * Mᴴ)ᴴ * (B * Mᴴ) := by
    rw [hB, Matrix.conjTranspose_mul, conjTranspose_conjTranspose]; simp only [Matrix.mul_assoc]
  have e2 : (B * Mᴴ) * (B * Mᴴ)ᴴ = B * Bᴴ := by
    rw [Matrix.conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc Mᴴ, hM, Matrix.one_mul]
  rw [e1, X5AF.T_swap, e2, ← X5AF.T_swap, hB]

end priv

section sep
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

lemma sep_of_sum {K : Type*} [Fintype K] (c : K → ℝ) (A : K → Matrix I I ℂ) (B : K → Matrix J J ℂ)
    (hc : ∀ k, 0 ≤ c k) (hc1 : ∑ k, c k = 1)
    (hAB : ∀ k, QAlgorithms.IsDensityMatrix (A k) ∧ QAlgorithms.IsDensityMatrix (B k)) :
    QAlgorithms.Entanglement.IsSeparableDensity (∑ k, (c k : ℂ) • Matrix.kronecker (A k) (B k)) := by
  set e := (Fintype.equivFin K).symm
  refine ⟨Fintype.card K, fun j => c (e j), fun j => A (e j), fun j => B (e j),
    fun j => hc _, ?_, fun j => hAB _, ?_⟩
  · rw [Equiv.sum_comp e c]; exact hc1
  · exact (Equiv.sum_comp e (fun k => (c k : ℂ) • Matrix.kronecker (A k) (B k))).symm
end sep

section final
open QAlgorithms.Papers.Independent.Dependency50.P24
variable {d : ℕ} [NeZero d] {S T' : Type*} [Fintype S] [Fintype T'] [DecidableEq S] [DecidableEq T']

end final

section bits
open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma bits_eq {ρ σ : Matrix I I ℂ} (hρ : QAlgorithms.IsDensityMatrix ρ)
    (hσ : QAlgorithms.IsDensityMatrix σ)
    (hker : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin) :
    relativeEntropyBits ρ σ = ENNReal.ofReal (X5PK.relEntropy ρ σ / Real.log 2) := by
  rw [relativeEntropyBits, dif_pos ⟨hρ, hσ⟩, QAlgorithms.QuantumLoss.umegakiEntropy, if_pos hker,
    ENNReal.ofReal_div_of_pos (Real.log_pos one_lt_two), X5PK.relEnt_def,
    X5QC.mul_log _ hρ.1.isHermitian]

lemma bits_ne_top {ρ σ : Matrix I I ℂ} (h : relativeEntropyBits ρ σ ≠ ⊤) :
    QAlgorithms.IsDensityMatrix ρ ∧ QAlgorithms.IsDensityMatrix σ ∧
      LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin := by
  unfold relativeEntropyBits at h
  split_ifs at h with h1
  · refine ⟨h1.1, h1.2, ?_⟩
    by_contra hk
    simp only [QAlgorithms.QuantumLoss.umegakiEntropy, hk, if_false] at h
    exact h (ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top)
  · simp at h
end bits

end X5PR
end X5mod_PR_Main

section X5mod_PN_Pin
open Matrix Finset Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PN
open X5QC X5PK
set_option linter.unusedSectionVars false

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- a complete family of orthogonal projections -/
structure PF (Q : K → Matrix H H ℂ) : Prop where
  herm : ∀ k, (Q k)ᴴ = Q k
  idem : ∀ k, Q k * Q k = Q k
  orth : ∀ k l, k ≠ l → Q k * Q l = 0
  compl : ∑ k, Q k = 1

/-- pinching -/
noncomputable def pinQ (Q : K → Matrix H H ℂ) (X : Matrix H H ℂ) : Matrix H H ℂ := ∑ k, Q k * X * Q k

variable {Q : K → Matrix H H ℂ}

lemma mul_pin (hQ : PF Q) (k : K) (X : Matrix H H ℂ) : Q k * pinQ Q X = Q k * X * Q k := by
  unfold pinQ; rw [Finset.mul_sum, Finset.sum_eq_single k]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ.idem]
  · intro l _ hl; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ.orth k l (Ne.symm hl)]; simp
  · simp

lemma pin_mul (hQ : PF Q) (k : K) (X : Matrix H H ℂ) : pinQ Q X * Q k = Q k * X * Q k := by
  unfold pinQ; rw [Finset.sum_mul, Finset.sum_eq_single k]
  · rw [Matrix.mul_assoc _ (Q k), hQ.idem]
  · intro l _ hl; rw [Matrix.mul_assoc _ (Q l), hQ.orth l k hl]; simp
  · simp

lemma comm_pin (hQ : PF Q) (k : K) (X : Matrix H H ℂ) : Commute (Q k) (pinQ Q X) := by
  show Q k * pinQ Q X = pinQ Q X * Q k
  rw [mul_pin hQ, pin_mul hQ]

lemma pin_pin (hQ : PF Q) (X : Matrix H H ℂ) : pinQ Q (pinQ Q X) = pinQ Q X := by
  show ∑ k, Q k * pinQ Q X * Q k = pinQ Q X
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_pin hQ, Matrix.mul_assoc _ (Q k), hQ.idem]

lemma tr_pin (hQ : PF Q) (X M : Matrix H H ℂ) (hM : ∀ k, Commute (Q k) M) :
    (pinQ Q X * M).trace = (X * M).trace := by
  have e : ∀ k, (Q k * X * Q k * M).trace = (X * M * Q k).trace := fun k => by
    rw [show Q k * X * Q k * M = Q k * (X * Q k * M) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, Matrix.mul_assoc X, (hM k).eq, Matrix.mul_assoc, Matrix.mul_assoc, hQ.idem,
      ← Matrix.mul_assoc]
  rw [pinQ, Finset.sum_mul, Matrix.trace_sum]
  simp only [e]
  rw [← Matrix.trace_sum, ← Finset.mul_sum, hQ.compl, Matrix.mul_one]

lemma pin_psd (hQ : PF Q) {X : Matrix H H ℂ} (hX : X.PosSemidef) : (pinQ Q X).PosSemidef := by
  unfold pinQ
  refine Matrix.posSemidef_sum _ fun k _ => ?_
  have := hX.conjTranspose_mul_mul_same (Q k)
  rwa [hQ.herm] at this

lemma pin_lin (hQ : PF Q) (a b : ℂ) (X : Matrix H H ℂ) :
    pinQ Q (a • X + b • 1) = a • pinQ Q X + b • 1 := by
  unfold pinQ
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    hQ.idem, Finset.sum_add_distrib, ← Finset.smul_sum, hQ.compl]

lemma pin_pe (hQ : PF Q) (ε : ℝ) (X : Matrix H H ℂ) : pinQ Q (pe ε X) = pe ε (pinQ Q X) :=
  pin_lin hQ _ _ X

lemma pinQ_trace (hQ : PF Q) (X : Matrix H H ℂ) : (pinQ Q X).trace = X.trace := by
  have := tr_pin hQ X 1 (fun k => Commute.one_right _)
  simpa using this

/-- vectors in the kernel of a pinched PSD matrix -/
lemma ker_aux (hQ : PF Q) {σ : Matrix H H ℂ} (hσ : σ.PosSemidef) {v : H → ℂ}
    (hv : pinQ Q σ *ᵥ v = 0) (k : K) : σ *ᵥ (Q k *ᵥ v) = 0 := by
  have e : ∀ l, star v ⬝ᵥ ((Q l * σ * Q l) *ᵥ v) = star (Q l *ᵥ v) ⬝ᵥ (σ *ᵥ (Q l *ᵥ v)) := by
    intro l
    rw [Matrix.star_mulVec, hQ.herm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec]
  have h0 : ∑ l, star (Q l *ᵥ v) ⬝ᵥ (σ *ᵥ (Q l *ᵥ v)) = 0 := by
    simp only [← e]
    rw [← dotProduct_sum, ← Matrix.sum_mulVec]
    rw [show (∑ l, Q l * σ * Q l) = pinQ Q σ from rfl, hv, dotProduct_zero]
  have hn : ∀ l ∈ Finset.univ, 0 ≤ star (Q l *ᵥ v) ⬝ᵥ (σ *ᵥ (Q l *ᵥ v)) :=
    fun l _ => hσ.dotProduct_mulVec_nonneg _
  have := (Finset.sum_eq_zero_iff_of_nonneg hn).1 h0 k (Finset.mem_univ _)
  exact (hσ.dotProduct_mulVec_zero_iff _).1 this

lemma ker_pin (hQ : PF Q) {ω σ : Matrix H H ℂ} (hσ : σ.PosSemidef)
    (hker : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ω.mulVecLin) :
    LinearMap.ker (pinQ Q σ).mulVecLin ≤ LinearMap.ker (pinQ Q ω).mulVecLin := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  have h : ∀ k, ω *ᵥ (Q k *ᵥ v) = 0 := fun k => by
    have := hker (show Q k *ᵥ v ∈ LinearMap.ker σ.mulVecLin by simpa using ker_aux hQ hσ hv k)
    simpa using this
  unfold pinQ
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

lemma ker_pin_self (hQ : PF Q) {ρ : Matrix H H ℂ} (hρ : ρ.PosSemidef) :
    LinearMap.ker (pinQ Q ρ).mulVecLin ≤ LinearMap.ker ρ.mulVecLin := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  have : v = ∑ k, Q k *ᵥ v := by rw [← Matrix.sum_mulVec, hQ.compl, Matrix.one_mulVec]
  rw [this, Matrix.mulVec_sum]
  exact Finset.sum_eq_zero fun k _ => ker_aux hQ hρ hv k

end X5PN
end X5mod_PN_Pin

section X5mod_PN_Dpi
open Matrix Finset Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PN
open X5QC X5PK
set_option linter.unusedSectionVars false

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- joint subadditivity, universe polymorphic -/
lemma jointT [Nonempty H] {A B C D : Matrix H H ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hC : C.PosDef) (hD : D.PosDef) :
    relEntropy (A + C) (B + D) ≤ relEntropy A B + relEntropy C D := by
  set e := (Fintype.equivFin H).symm
  haveI : NeZero (Fintype.card H) := ⟨Fintype.card_ne_zero⟩
  have h := joint (hA.submatrix e.injective) (hB.submatrix e.injective)
    (hC.submatrix e.injective) (hD.submatrix e.injective)
  have sa : ∀ M N : Matrix H H ℂ, M.submatrix e e + N.submatrix e e = (M + N).submatrix e e :=
    fun M N => by ext; simp
  rwa [sa, sa,
    relEnt_sub (hA.add hC).isHermitian (hB.add hD).isHermitian e,
    relEnt_sub hA.isHermitian hB.isHermitian e, relEnt_sub hC.isHermitian hD.isHermitian e] at h

/-- binary pinching -/
def bin (P X : Matrix H H ℂ) : Matrix H H ℂ := P * X * P + (1 - P) * X * (1 - P)

lemma two_bin (P X : Matrix H H ℂ) :
    X + (P + P - 1) * X * (P + P - 1) = (2 : ℝ) • bin P X := by
  rw [two_smul]; unfold bin; noncomm_ring

lemma V_sq {P : Matrix H H ℂ} (hi : P * P = P) : (P + P - 1) * (P + P - 1) = 1 := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, hi, Matrix.one_mul,
    Matrix.mul_one]
  abel

lemma V_inj {P : Matrix H H ℂ} (hi : P * P = P) : Function.Injective (P + P - 1).vecMul := by
  intro v w h
  have := congrArg (fun u => u ᵥ* (P + P - 1)) h
  simpa only [Matrix.vecMul_vecMul, V_sq hi, Matrix.vecMul_one] using this

lemma V_posDef {P X : Matrix H H ℂ} (hh : Pᴴ = P) (hi : P * P = P) (hX : X.PosDef) :
    ((P + P - 1) * X * (P + P - 1)).PosDef := by
  have := hX.mul_mul_conjTranspose_same (V_inj hi)
  rwa [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, hh, Matrix.conjTranspose_one] at this

lemma bin_posDef {P X : Matrix H H ℂ} (hh : Pᴴ = P) (hi : P * P = P) (hX : X.PosDef) :
    (bin P X).PosDef := by
  have h := (hX.add (V_posDef hh hi hX)).smul (show (0 : ℝ) < 1 / 2 by norm_num)
  rwa [two_bin, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h

lemma bin_dpi [Nonempty H] {P X Y : Matrix H H ℂ} (hh : Pᴴ = P) (hi : P * P = P)
    (hX : X.PosDef) (hY : Y.PosDef) : relEntropy (bin P X) (bin P Y) ≤ relEntropy X Y := by
  have h := jointT hX hY (V_posDef hh hi hX) (V_posDef hh hi hY)
  have hs : star (P + P - 1) = P + P - 1 := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_sub, Matrix.conjTranspose_add, hh,
      Matrix.conjTranspose_one]
  have hU : (P + P - 1) ∈ unitary (Matrix H H ℂ) :=
    ⟨by rw [hs]; exact V_sq hi, by rw [hs]; exact V_sq hi⟩
  have hc := relEnt_conj ⟨_, hU⟩ hX.isHermitian hY.isHermitian
  simp only [hs] at hc
  rw [hc, two_bin, two_bin, relEnt_smul (bin_posDef hh hi hX) (bin_posDef hh hi hY) two_pos
    two_pos, sub_self, mul_zero, add_zero] at h
  linarith

variable {Q : K → Matrix H H ℂ}

/-- partial pinching over a finset -/
noncomputable def pS (Q : K → Matrix H H ℂ) (s : Finset K) (X : Matrix H H ℂ) : Matrix H H ℂ :=
  ∑ k ∈ s, Q k * X * Q k + (1 - ∑ k ∈ s, Q k) * X * (1 - ∑ k ∈ s, Q k)

lemma pS_insert (hQ : PF Q) {a : K} {s : Finset K} (ha : a ∉ s) (X : Matrix H H ℂ) :
    pS Q (insert a s) X = bin (Q a) (pS Q s X) := by
  set T := ∑ k ∈ s, Q k * X * Q k
  set R := 1 - ∑ k ∈ s, Q k
  have hne : ∀ k ∈ s, a ≠ k := fun k hk h => ha (h ▸ hk)
  have h1 : Q a * T = 0 := by
    rw [Finset.mul_sum]; refine Finset.sum_eq_zero fun k hk => ?_
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ.orth a k (hne k hk)]; simp
  have h2 : T * Q a = 0 := by
    rw [Finset.sum_mul]; refine Finset.sum_eq_zero fun k hk => ?_
    rw [Matrix.mul_assoc _ (Q k), hQ.orth k a (hne k hk).symm]; simp
  have h3 : Q a * R = Q a := by
    rw [Matrix.mul_sub, Matrix.mul_one, Finset.mul_sum,
      Finset.sum_eq_zero fun k hk => hQ.orth a k (hne k hk), sub_zero]
  have h4 : R * Q a = Q a := by
    rw [Matrix.sub_mul, Matrix.one_mul, Finset.sum_mul,
      Finset.sum_eq_zero fun k hk => hQ.orth k a (hne k hk).symm, sub_zero]
  have hZ1 : Q a * (T + R * X * R) = Q a * X * R := by
    rw [Matrix.mul_add, h1, zero_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h3]
  have hZ2 : (T + R * X * R) * Q a = R * X * Q a := by
    rw [Matrix.add_mul, h2, zero_add, Matrix.mul_assoc _ R, h4]
  have hR : 1 - ∑ k ∈ insert a s, Q k = R - Q a := by
    rw [Finset.sum_insert ha]; simp only [R]; abel
  have hb : ∀ Z : Matrix H H ℂ, bin (Q a) Z = Q a * Z * Q a + Z - Q a * Z - Z * Q a + Q a * Z * Q a :=
    fun Z => by unfold bin; noncomm_ring
  show _ = bin (Q a) (T + R * X * R)
  rw [hb, hZ1, hZ2, Matrix.mul_assoc (Q a * X) R (Q a), h4]
  unfold pS
  rw [hR, Finset.sum_insert ha]
  simp only [T]
  noncomm_ring

lemma pS_dpi [Nonempty H] (hQ : PF Q) (s : Finset K) {X Y : Matrix H H ℂ} (hX : X.PosDef)
    (hY : Y.PosDef) :
    (pS Q s X).PosDef ∧ (pS Q s Y).PosDef ∧ relEntropy (pS Q s X) (pS Q s Y) ≤ relEntropy X Y := by
  induction s using Finset.induction_on with
  | empty => simpa [pS] using ⟨hX, hY⟩
  | insert a s ha ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    rw [pS_insert hQ ha, pS_insert hQ ha]
    exact ⟨bin_posDef (hQ.herm a) (hQ.idem a) i1, bin_posDef (hQ.herm a) (hQ.idem a) i2,
      (bin_dpi (hQ.herm a) (hQ.idem a) i1 i2).trans i3⟩

lemma pS_univ (hQ : PF Q) (X : Matrix H H ℂ) : pS Q Finset.univ X = pinQ Q X := by
  simp [pS, pinQ, hQ.compl]

/-- data processing for pinching, positive definite case -/
lemma dpi_pd [Nonempty H] (hQ : PF Q) {X Y : Matrix H H ℂ} (hX : X.PosDef) (hY : Y.PosDef) :
    relEntropy (pinQ Q X) (pinQ Q Y) ≤ relEntropy X Y := by
  have := (pS_dpi hQ Finset.univ hX hY).2.2
  rwa [pS_univ hQ, pS_univ hQ] at this

/-- data processing for pinching under the support condition -/
theorem dpi [Nonempty H] (hQ : PF Q) {X Y : Matrix H H ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hker : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin) :
    relEntropy (pinQ Q X) (pinQ Q Y) ≤ relEntropy X Y := by
  have t1 := cont (pin_psd hQ hX) (pin_psd hQ hY) (ker_pin hQ hY hker) 1
  have t2 := cont hX hY hker 1
  refine le_of_tendsto_of_tendsto (t1.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0)))
    (t2.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))) ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hε' : 0 < 1 * ε := by linarith
  rw [← pin_pe hQ, ← pin_pe hQ]
  exact dpi_pd hQ (pe_posDef hX hε') (pe_posDef hY hε')

end X5PN
end X5mod_PN_Dpi

section X5mod_PN_Ent
open Matrix Finset Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PN
open X5QC X5PK X5AF
set_option linter.unusedSectionVars false

/-- Araki–Lieb: `S(B) ≤ S(A) + S(AB)` -/
lemma araki {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {rho : Matrix (A × B) (A × B) ℂ} (h : QAlgorithms.IsDensityMatrix rho) :
    QAlgorithms.vnEntropy (QAlgorithms.traceLeft rho) ≤
      QAlgorithms.vnEntropy (QAlgorithms.traceRight rho) + QAlgorithms.vnEntropy rho := by
  set τ := ((Mp rho)ᴴ * Mp rho)ᵀ
  have hτ : QAlgorithms.IsDensityMatrix τ := by
    refine ⟨(Matrix.posSemidef_conjTranspose_mul_self _).transpose, ?_⟩
    rw [Matrix.trace_transpose, Matrix.trace_mul_comm, Mp_mul h.1, tr_traceLeft, h.2]
  have h1 := QAlgorithms.Arunachalam.vnEntropy_subadditive τ hτ
  rw [tau_trR h.1, tau_trL h.1] at h1
  have e1 : QAlgorithms.vnEntropy τ = QAlgorithms.vnEntropy (QAlgorithms.traceLeft rho) := by
    rw [vn_eq, vn_eq, T_transpose (Matrix.isHermitian_conjTranspose_mul_self _), T_swap, Mp_mul h.1]
  have e2 : QAlgorithms.vnEntropy rhoᵀ = QAlgorithms.vnEntropy rho := by
    rw [vn_eq, vn_eq, T_transpose h.1.1]
  linarith

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
variable {Q : K → Matrix H H ℂ}

/-- the isometry `v ↦ ∑ₖ |k⟩ ⊗ Qₖ v` -/
def W (Q : K → Matrix H H ℂ) : Matrix (K × H) H ℂ := fun a y => Q a.1 a.2 y

lemma W_iso (hQ : PF Q) : (W Q)ᴴ * W Q = 1 := by
  have : (W Q)ᴴ * W Q = ∑ k, (Q k)ᴴ * Q k := by
    ext x y
    simp [Matrix.mul_apply, W, Fintype.sum_prod_type, Matrix.sum_apply]
  rw [this]
  simp only [hQ.herm, hQ.idem, hQ.compl]

lemma W_apply (ρ : Matrix H H ℂ) (hQ : PF Q) (k l : K) (x y : H) :
    (W Q * ρ * (W Q)ᴴ) (k, x) (l, y) = (Q k * ρ * Q l) x y := by
  conv_rhs => rw [← hQ.herm l]
  simp [Matrix.mul_apply, W]

lemma W_trL (ρ : Matrix H H ℂ) (hQ : PF Q) :
    QAlgorithms.traceLeft (W Q * ρ * (W Q)ᴴ) = pinQ Q ρ := by
  ext x y
  simp only [QAlgorithms.traceLeft, Matrix.of_apply, W_apply ρ hQ, pinQ, Matrix.sum_apply]

lemma tr_Q {ρ : Matrix H H ℂ} (hρ : ρ.PosSemidef) (hQ : PF Q) (k : K) :
    (Q k * ρ).trace = (((Q k * ρ).trace.re : ℝ) : ℂ) := by
  have hp : (Q k * ρ * Q k).PosSemidef := by
    have := hρ.conjTranspose_mul_mul_same (Q k); rwa [hQ.herm] at this
  have e : (Q k * ρ * Q k).trace = (Q k * ρ).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQ.idem]
  have := hp.trace_nonneg
  rw [e] at this
  exact Complex.ext rfl (by simpa using (Complex.nonneg_iff.1 this).2.symm)

lemma W_trR {ρ : Matrix H H ℂ} (hρ : ρ.PosSemidef) (hQ : PF Q) :
    QAlgorithms.traceRight (W Q * ρ * (W Q)ᴴ) =
      diagonal (fun k => ((((Q k * ρ).trace.re : ℝ)) : ℂ)) := by
  ext k l
  simp only [QAlgorithms.traceRight, Matrix.of_apply, W_apply ρ hQ]
  have : ∑ x, (Q k * ρ * Q l) x x = (Q l * Q k * ρ).trace := by
    rw [show (∑ x, (Q k * ρ * Q l) x x) = (Q k * ρ * Q l).trace from rfl, Matrix.trace_mul_comm,
      Matrix.mul_assoc]
  rw [this]
  by_cases hkl : k = l
  · subst hkl; rw [hQ.idem, diagonal_apply_eq, ← tr_Q hρ hQ]
  · rw [hQ.orth l k (Ne.symm hkl), Matrix.zero_mul, Matrix.trace_zero, diagonal_apply_ne _ hkl]

lemma T_diag (p : K → ℝ) :
    T (diagonal (fun k => ((p k : ℝ) : ℂ))) = ∑ k, p k * Real.log (p k) := by
  unfold T
  rw [cfc_diag, Matrix.trace_diagonal, Complex.re_sum]
  simp

lemma T_pin_eq (hQ : PF Q) {ρ : Matrix H H ℂ} (hρ : ρ.PosSemidef) :
    relEntropy ρ (pinQ Q ρ) = T ρ - T (pinQ Q ρ) := by
  have hc : ∀ k, Commute (Q k) (cfc Real.log (pinQ Q ρ)) := fun k =>
    ((comm_pin hQ k ρ).symm.cfc_real Real.log).symm
  rw [relEnt_def, Matrix.trace_sub, Complex.sub_re, ← tr_pin hQ ρ _ hc, mul_log _ hρ.1,
    mul_log _ (pin_psd hQ hρ).1]
  rfl

/-- `D(ρ ‖ P ρ) ≤ H(p)` in nats -/
theorem pin_ent [Nonempty H] (hQ : PF Q) {ρ : Matrix H H ℂ} (hρ : QAlgorithms.IsDensityMatrix ρ) :
    relEntropy ρ (pinQ Q ρ) ≤ ∑ k, -((Q k * ρ).trace.re * Real.log ((Q k * ρ).trace.re)) := by
  set ω := W Q * ρ * (W Q)ᴴ
  have hω : QAlgorithms.IsDensityMatrix ω := by
    refine ⟨hρ.1.mul_mul_conjTranspose_same _, ?_⟩
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, W_iso hQ, Matrix.one_mul, hρ.2]
  have h := araki hω
  rw [W_trL ρ hQ, W_trR hρ.1 hQ] at h
  have e : QAlgorithms.vnEntropy ω = QAlgorithms.vnEntropy ρ := by
    rw [vn_eq, vn_eq, X5PR.T_iso hρ.1 _ (W_iso hQ)]
  rw [e, vn_eq, vn_eq, vn_eq, T_diag] at h
  rw [T_pin_eq hQ hρ.1, Finset.sum_neg_distrib]
  have hl := Real.log_pos one_lt_two
  rw [← add_div, div_le_div_iff_of_pos_right hl] at h
  linarith

end X5PN
end X5mod_PN_Ent

section X5mod_PN_Main
open Matrix Finset Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker ENNReal

namespace X5PN
open X5QC X5PK QAlgorithms.Papers.Independent.Information100.P54
set_option linter.unusedSectionVars false

lemma ofReal_sum_le' {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ENNReal.ofReal_add_le.trans (add_le_add_right ih _)

section gen
variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
variable {Q : K → Matrix H H ℂ}

lemma relEnt_split (hQ : PF Q) (ρ τ : Matrix H H ℂ) :
    relEntropy ρ (pinQ Q τ) = relEntropy ρ (pinQ Q ρ) + relEntropy (pinQ Q ρ) (pinQ Q τ) := by
  have hc : ∀ X : Matrix H H ℂ, ∀ k, Commute (Q k) (cfc Real.log (pinQ Q X)) := fun X k =>
    ((comm_pin hQ k X).symm.cfc_real _).symm
  simp only [relEnt_def, Matrix.trace_sub, Complex.sub_re]
  rw [← tr_pin hQ ρ _ (hc τ), ← tr_pin hQ ρ _ (hc ρ)]
  ring
end gen

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J]
  [DecidableEq K]

/-- Bob's projections on `I × J` -/
def Qb (P : K → Matrix J J ℂ) : K → Matrix (I × J) (I × J) ℂ :=
  fun k => (1 : Matrix I I ℂ) ⊗ₖ P k

lemma PF_P {P : K → Matrix J J ℂ} (hself : ∀ k, (P k).conjTranspose = P k)
    (hproj : ∀ k, P k * P k = P k) (horth : ∀ k l, k ≠ l → P k * P l = 0)
    (hcomplete : ∑ k, P k = 1) : PF P := ⟨hself, hproj, horth, hcomplete⟩

lemma PF_Qb {P : K → Matrix J J ℂ} (hP : PF P) : PF (Qb (I := I) P) where
  herm k := by simp only [Qb, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hP.herm]
  idem k := by rw [Qb, ← Matrix.mul_kronecker_mul, Matrix.one_mul, hP.idem]
  orth k l h := by simp only [Qb]; rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, hP.orth k l h,
    Matrix.kronecker_zero]
  compl := by
    rw [← Matrix.one_kronecker_one, ← hP.compl]
    ext a b
    simp [Qb, Matrix.kronecker_apply, Matrix.sum_apply, Finset.mul_sum]

lemma bob_eq {P : K → Matrix J J ℂ} (hP : PF P) (rho : Matrix (I × J) (I × J) ℂ) :
    bobPinching P rho = pinQ (Qb P) rho := by
  unfold bobPinching pinQ
  refine Finset.sum_congr rfl fun k _ => ?_
  show Qb P k * rho * (Qb P k)ᴴ = _
  rw [(PF_Qb (I := I) hP).herm k]

lemma sep_pin [Nonempty I] [Nonempty J] {P : K → Matrix J J ℂ} (hP : PF P)
    {σ : Matrix (I × J) (I × J) ℂ} (hσ : QAlgorithms.Entanglement.IsSeparableDensity σ) :
    QAlgorithms.Entanglement.IsSeparableDensity (pinQ (Qb P) σ) := by
  obtain ⟨q, w, A, B, hw0, hw1, hAB, rfl⟩ := hσ
  set M : Fin q → K → Matrix J J ℂ := fun j k => P k * B j * P k
  have hM : ∀ j k, (M j k).PosSemidef := fun j k => by
    have := (hAB j).2.1.conjTranspose_mul_mul_same (P k); rwa [hP.herm] at this
  set t : Fin q → K → ℝ := fun j k => (M j k).trace.re
  have ht0 : ∀ j k, 0 ≤ t j k := fun j k => (Complex.nonneg_iff.1 (hM j k).trace_nonneg).1
  have htr : ∀ j k, (M j k).trace = ((t j k : ℝ) : ℂ) := fun j k => tr_re (hM j k)
  have ht1 : ∀ j, ∑ k, t j k = 1 := fun j => by
    have := pinQ_trace hP (B j)
    rw [(hAB j).2.2] at this
    have e : ∑ k, t j k = ((∑ k, M j k).trace).re := by
      rw [Matrix.trace_sum, Complex.re_sum]
    rw [e, show (∑ k, M j k) = pinQ P (B j) from rfl, this, Complex.one_re]
  set B' : Fin q → K → Matrix J J ℂ := fun j k => if t j k = 0 then B j else (t j k)⁻¹ • M j k
  have key : pinQ (Qb P) (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)) =
      ∑ x : Fin q × K, ((w x.1 * t x.1 x.2 : ℝ) : ℂ) • Matrix.kronecker (A x.1) (B' x.1 x.2) := by
    unfold Matrix.kronecker
    rw [Fintype.sum_prod_type]
    unfold pinQ
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, Qb, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one]
    by_cases h0 : t j k = 0
    · have hz : M j k = 0 := (hM j k).trace_eq_zero_iff.1 (by rw [htr, h0]; simp)
      simp only [B', h0, if_true, mul_zero, Complex.ofReal_zero, zero_smul]
      rw [show P k * B j * P k = M j k from rfl, hz, Matrix.kronecker_zero, smul_zero]
    · simp only [B', h0, if_false]
      have h0' : ((t j k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0
      ext a b
      simp only [Matrix.smul_apply, Matrix.kroneckerMap_apply, smul_eq_mul, Complex.real_smul,
        Complex.ofReal_mul, Complex.ofReal_inv]
      field_simp
      rfl
  unfold Matrix.kronecker at key ⊢
  rw [key]
  refine X5PR.sep_of_sum _ _ _ (fun x => mul_nonneg (hw0 _) (ht0 _ _)) ?_ fun x => ⟨(hAB x.1).1, ?_⟩
  · rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ht1, mul_one, hw1]
  · by_cases h0 : t x.1 x.2 = 0
    · simp only [B', h0, if_true]; exact (hAB x.1).2
    · simp only [B', h0, if_false]
      refine ⟨(hM _ _).smul (inv_nonneg.2 (ht0 _ _)), ?_⟩
      rw [Matrix.trace_smul, htr, Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ h0,
        Complex.ofReal_one]

theorem p54_main [Nonempty I] [Nonempty J]
    (rho : Matrix (I × J) (I × J) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho)
    (P : K → Matrix J J ℂ) (hself : ∀ k, (P k).conjTranspose = P k)
    (hproj : ∀ k, P k * P k = P k)
    (horth : ∀ k l, k ≠ l → P k * P l = 0) (hcomplete : ∑ k, P k = 1) :
    relativeEntanglement rho ≤ relativeEntanglement (bobPinching P rho) +
      relativeEntropyBits rho (bobPinching P rho) ∧
    relativeEntanglement (bobPinching P rho) + relativeEntropyBits rho (bobPinching P rho) ≤
      relativeEntanglement (bobPinching P rho) + shannonEntropy (pinchingProbability P rho) := by
  have hP := PF_P hself hproj horth hcomplete
  have hQ := PF_Qb (I := I) hP
  set Q := Qb (I := I) P
  rw [bob_eq hP]
  have hpd : QAlgorithms.IsDensityMatrix (pinQ Q rho) :=
    ⟨pin_psd hQ hrho.1, by rw [pinQ_trace hQ, hrho.2]⟩
  have hk0 := ker_pin_self hQ hrho.1
  have hD := X5PR.bits_eq hrho hpd hk0
  have hl := Real.log_pos one_lt_two
  constructor
  · conv_rhs => unfold relativeEntanglement
    rw [ENNReal.sInf_add]
    refine le_iInf₂ fun e he => ?_
    obtain ⟨σ, hσ, rfl⟩ := he
    by_cases ht : relativeEntropyBits (pinQ Q rho) σ = ⊤
    · rw [ht, top_add]; exact le_top
    obtain ⟨_, hσd, hkσ⟩ := X5PR.bits_ne_top ht
    have hsep := sep_pin hP hσ
    have hPσd : QAlgorithms.IsDensityMatrix (pinQ Q σ) :=
      ⟨pin_psd hQ hσd.1, by rw [pinQ_trace hQ, hσd.2]⟩
    have k1 := ker_pin hQ hσd.1 hkσ
    rw [pin_pin hQ] at k1
    have k2 := k1.trans hk0
    have hdpi := dpi hQ hpd.1 hσd.1 hkσ
    rw [pin_pin hQ] at hdpi
    have hsplit := relEnt_split hQ rho σ
    calc relativeEntanglement rho ≤ relativeEntropyBits rho (pinQ Q σ) :=
          sInf_le ⟨_, hsep, rfl⟩
      _ = ENNReal.ofReal (relEntropy rho (pinQ Q σ) / Real.log 2) := X5PR.bits_eq hrho hPσd k2
      _ ≤ ENNReal.ofReal (relEntropy (pinQ Q rho) σ / Real.log 2 +
            relEntropy rho (pinQ Q rho) / Real.log 2) := by
          apply ENNReal.ofReal_le_ofReal
          rw [← add_div]
          exact div_le_div_of_nonneg_right (by linarith) hl.le
      _ ≤ _ := ENNReal.ofReal_add_le
      _ = _ := by rw [X5PR.bits_eq hpd hσd hkσ, hD]
  · refine add_le_add le_rfl ?_
    rw [hD, shannonEntropy, tsum_fintype]
    have hx : ∀ k, 0 ≤ (Q k * rho).trace.re := fun k => by
      have hp : (Q k * rho * Q k).PosSemidef := by
        have := hrho.1.conjTranspose_mul_mul_same (Q k); rwa [hQ.herm] at this
      have e : (Q k * rho * Q k).trace = (Q k * rho).trace := by
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQ.idem]
      rw [← e]; exact (Complex.nonneg_iff.1 hp.trace_nonneg).1
    have hpk : ∀ k, (pinchingProbability P rho k).toReal = (Q k * rho).trace.re := fun k =>
      ENNReal.toReal_ofReal (hx k)
    simp only [hpk]
    refine le_trans ?_ (ofReal_sum_le' _ _)
    apply ENNReal.ofReal_le_ofReal
    have := pin_ent hQ hrho
    rw [← Finset.sum_div]
    refine div_le_div_of_nonneg_right ?_ hl.le
    simpa only [neg_mul] using this

end X5PN
end X5mod_PN_Main

noncomputable section
open scoped ENNReal Matrix
open Filter
attribute [local instance] Classical.propDecidable
open QAlgorithms.Papers.Independent.Information100.P54

theorem solution {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [Nonempty I] [Nonempty J]
    (rho : Matrix (I × J) (I × J) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho)
    (P : K → Matrix J J ℂ) (hself : ∀ k, (P k).conjTranspose = P k)
    (hproj : ∀ k, P k * P k = P k)
    (horth : ∀ k l, k ≠ l → P k * P l = 0) (hcomplete : ∑ k, P k = 1) :
    relativeEntanglement rho ≤ relativeEntanglement (bobPinching P rho) +
      relativeEntropyBits rho (bobPinching P rho) ∧
    relativeEntanglement (bobPinching P rho) + relativeEntropyBits rho (bobPinching P rho) ≤
      relativeEntanglement (bobPinching P rho) + shannonEntropy (pinchingProbability P rho) :=
  X5PN.p54_main rho hrho P hself hproj horth hcomplete

end
