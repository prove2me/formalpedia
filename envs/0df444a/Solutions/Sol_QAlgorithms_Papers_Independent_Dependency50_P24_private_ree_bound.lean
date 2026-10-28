-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P24.private_ree_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:32:21.739509+00:00
-- url     : https://prove2.me/submissions/021a266d-1ede-44d5-bb29-5d83ae46a94d

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12
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

/-- conjugation by an isometry as a non-unital star algebra hom -/
noncomputable def x5ai_conjHom {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix n m ℂ) (hW : Wᴴ * W = 1) : Matrix m m ℂ →⋆ₙₐ[ℂ] Matrix n n ℂ where
  toFun X := W * X * Wᴴ
  map_smul' c X := by simp
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_mul' X Y := by
    calc W * (X * Y) * Wᴴ = W * X * (Wᴴ * W) * Y * Wᴴ := by rw [hW]; simp [Matrix.mul_assoc]
      _ = _ := by simp [Matrix.mul_assoc]
  map_star' X := by simp [Matrix.star_eq_conjTranspose, conjTranspose_mul, Matrix.mul_assoc]

theorem x5ai_finite_cont {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (quasispectrum ℝ M) := by
  have : (quasispectrum ℝ M).Finite := by
    rw [quasispectrum_eq_spectrum_union_zero]
    exact (M.finite_real_spectrum).union (Set.finite_singleton 0)
  exact this.continuousOn _

theorem x5ai_conj {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix n m ℂ) (hW : Wᴴ * W = 1) (M : Matrix m m ℂ) (hM : M.IsHermitian)
    (f : ℝ → ℝ) (hf : f 0 = 0) : cfc f (W * M * Wᴴ) = W * cfc f M * Wᴴ := by
  have hWM : (W * M * Wᴴ).IsHermitian := by
    simp [IsHermitian, conjTranspose_mul, hM.eq, Matrix.mul_assoc]
  have hc : Continuous (x5ai_conjHom W hW) := by
    change Continuous fun X : Matrix m m ℂ => W * X * Wᴴ; fun_prop
  have h := NonUnitalStarAlgHom.map_cfcₙ (R := ℝ) (S := ℂ) (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    (x5ai_conjHom W hW) f M (x5ai_finite_cont M f) hf hc hM.isSelfAdjoint hWM.isSelfAdjoint
  have h2 : W * cfcₙ f M * Wᴴ = cfcₙ f (W * M * Wᴴ) := h
  have e1 : cfcₙ f M = cfc f M := cfcₙ_eq_cfc (x5ai_finite_cont M f) hf
  have e2 : cfcₙ f (W * M * Wᴴ) = cfc f (W * M * Wᴴ) := cfcₙ_eq_cfc (x5ai_finite_cont (W * M * Wᴴ) f) hf
  rw [← e1, ← e2, h2]

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

lemma spec {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    X = (hX.eigenvectorUnitary : Matrix ι ι ℂ) * diagonal (fun k => ((hX.eigenvalues k : ℝ) : ℂ)) *
      (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  conv_lhs => rw [← cfc_id' ℝ X hX.isSelfAdjoint]
  rw [hX.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

lemma cfc_spec {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    cfc f X = (hX.eigenvectorUnitary : Matrix ι ι ℂ) * diagonal (fun k => ((f (hX.eigenvalues k) : ℝ) : ℂ)) *
      (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  rw [hX.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

lemma uu {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * (hX.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
  Unitary.coe_star_mul_self _

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

open X5AD in
theorem cfc_kron2 {X : Matrix ι ι ℂ} {Y : Matrix κ κ ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (f g1 h1 g2 h2 : ℝ → ℝ) (hf0 : f 0 = 0)
    (hsplit : ∀ x y, 0 ≤ x → 0 ≤ y → f (x * y) = g1 x * h1 y + g2 x * h2 y) :
    cfc f (X ⊗ₖ Y) = cfc g1 X ⊗ₖ cfc h1 Y + cfc g2 X ⊗ₖ cfc h2 Y := by
  have hXh := hX.isHermitian
  have hYh := hY.isHermitian
  set U := (hXh.eigenvectorUnitary : Matrix ι ι ℂ)
  set V := (hYh.eigenvectorUnitary : Matrix κ κ ℂ)
  set d := hXh.eigenvalues
  set e := hYh.eigenvalues
  have hW : (U ⊗ₖ V)ᴴ * (U ⊗ₖ V) = 1 := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, uu hXh, uu hYh, one_kronecker_one]
  have hDE : diagonal (fun k => ((d k : ℝ) : ℂ)) ⊗ₖ diagonal (fun k => ((e k : ℝ) : ℂ)) =
      diagonal (fun p : ι × κ => ((d p.1 * e p.2 : ℝ) : ℂ)) := by
    rw [diagonal_kronecker_diagonal]; congr 1; ext p; simp
  have hXY : X ⊗ₖ Y = (U ⊗ₖ V) * diagonal (fun p : ι × κ => ((d p.1 * e p.2 : ℝ) : ℂ)) * (U ⊗ₖ V)ᴴ := by
    conv_lhs => rw [spec hXh, spec hYh]
    rw [← hDE, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]
  have hDh : (diagonal (fun p : ι × κ => ((d p.1 * e p.2 : ℝ) : ℂ))).IsHermitian :=
    isHermitian_diagonal_of_self_adjoint _ (by ext k; simp [Complex.conj_ofReal])
  rw [hXY, x5ai_conj (U ⊗ₖ V) hW _ hDh f hf0, cfc_diag (fun p : ι × κ => d p.1 * e p.2) f,
    cfc_spec hXh, cfc_spec hYh, cfc_spec hXh, cfc_spec hYh]
  have hd : ∀ k, 0 ≤ d k := hX.eigenvalues_nonneg
  have he : ∀ k, 0 ≤ e k := hY.eigenvalues_nonneg
  have hDE' : diagonal (fun p : ι × κ => ((f (d p.1 * e p.2) : ℝ) : ℂ)) =
      diagonal (fun k => ((g1 (d k) : ℝ) : ℂ)) ⊗ₖ diagonal (fun k => ((h1 (e k) : ℝ) : ℂ)) +
      diagonal (fun k => ((g2 (d k) : ℝ) : ℂ)) ⊗ₖ diagonal (fun k => ((h2 (e k) : ℝ) : ℂ)) := by
    rw [diagonal_kronecker_diagonal, diagonal_kronecker_diagonal, diagonal_add]; congr 1; ext p
    simp [hsplit _ _ (hd p.1) (he p.2)]
  rw [hDE', Matrix.mul_add, Matrix.add_mul, conjTranspose_kronecker, ← mul_kronecker_mul,
    ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul]

end X5QC
end X5mod_QC_Kron

section X5mod_QC_Supp
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def ind (x : ℝ) : ℝ := if x = 0 then 0 else 1

noncomputable def supp (X : Matrix ι ι ℂ) : Matrix ι ι ℂ := cfc ind X

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

lemma cfc_log_smul {p : ℝ} (hp : 0 < p) (Y : Matrix ι ι ℂ) (hY : Y.IsHermitian) :
    cfc Real.log ((p : ℂ) • Y) = ((Real.log p : ℝ) : ℂ) • supp Y + cfc Real.log Y := by
  rw [real_smul, ← cfc_comp_smul p _ Y ((Y.finite_real_spectrum.image _).continuousOn _) hY.isSelfAdjoint, real_smul, supp,
    ← cfc_smul _ _ _ (X5B2.fin _ _), ← cfc_add _ _ _ (X5B2.fin _ _) (X5B2.fin _ _)]
  refine cfc_congr fun x _ => ?_
  simp only [smul_eq_mul, ind]
  by_cases hx : x = 0
  · subst hx; simp
  rw [if_neg hx, Real.log_mul hp.ne' hx]; ring

lemma log_kron {Y : Matrix ι ι ℂ} {Z : Matrix κ κ ℂ} (hY : Y.PosSemidef) (hZ : Z.PosSemidef) :
    cfc Real.log (Y ⊗ₖ Z) = cfc Real.log Y ⊗ₖ supp Z + supp Y ⊗ₖ cfc Real.log Z :=
  cfc_kron2 hY hZ Real.log Real.log ind ind Real.log Real.log_zero (fun x y _ _ => by
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [ind, hx, hy, Real.log_mul])

/-- `Tr (X log X)`, in nats. -/
noncomputable def T (X : Matrix ι ι ℂ) : ℝ := (cfc (fun x : ℝ => x * Real.log x) X).trace.re

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

lemma tr_cfc_sub {X : Matrix m m ℂ} (hX : X.IsHermitian) (e : n ≃ m) (f : ℝ → ℝ) :
    (cfc f (X.submatrix e e)).trace = (cfc f X).trace := by
  have hA : IsSelfAdjoint (X.submatrix e e) := (hX.submatrix e).isSelfAdjoint
  have hB : IsSelfAdjoint X := hX.isSelfAdjoint
  have fA : (spectrum ℝ (X.submatrix e e)).Finite := (X.submatrix e e).finite_real_spectrum
  have fB : (spectrum ℝ X).Finite := X.finite_real_spectrum
  set s : Finset ℝ := fA.toFinset ∪ fB.toFinset
  set p := Lagrange.interpolate s (fun x : ℝ => x) f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  have h1 : cfc f (X.submatrix e e) = cfc (fun x => p.eval x) (X.submatrix e e) :=
    cfc_congr fun x hx => (hp x (by simp [s, fA.mem_toFinset.2 hx])).symm
  have h2 : cfc f X = cfc (fun x => p.eval x) X :=
    cfc_congr fun x hx => (hp x (by simp [s, fB.mem_toFinset.2 hx])).symm
  rw [h1, h2, cfc_polynomial p _ hA, cfc_polynomial p X hB, aeval_sub_equiv, trace_sub_equiv]

lemma traceNorm_sub (Z : Matrix m m ℂ) (e : n ≃ m) :
    QAlgorithms.traceNorm (Z.submatrix e e) = QAlgorithms.traceNorm Z := by
  unfold QAlgorithms.traceNorm
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    tr_cfc_sub (Matrix.isHermitian_conjTranspose_mul_self Z)]

lemma dens_sub {X : Matrix m m ℂ} (hX : QAlgorithms.IsDensityMatrix X) (e : n ≃ m) :
    QAlgorithms.IsDensityMatrix (X.submatrix e e) :=
  ⟨hX.1.submatrix e, (trace_sub_equiv e X).trans hX.2⟩

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

lemma supp_posDef {X : Matrix n n ℂ} (hX : X.PosDef) : supp X = 1 := by
  unfold supp
  rw [← cfc_one ℝ X hX.isHermitian.isSelfAdjoint]
  refine cfc_congr fun x hx => ?_
  obtain ⟨i, rfl⟩ := hX.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
  simp [ind, (hX.eigenvalues_pos i).ne']

lemma relEnt_kron {ρ σ : Matrix m m ℂ} {τ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hτ : τ.PosDef) (htr : τ.trace = 1) :
    relEntropy (ρ ⊗ₖ τ) (σ ⊗ₖ τ) = relEntropy ρ σ := by
  rw [relEnt_def, relEnt_def, log_kron hρ.posSemidef hτ.posSemidef,
    log_kron hσ.posSemidef hτ.posSemidef, supp_posDef hρ, supp_posDef hσ, supp_posDef hτ]
  simp only [Matrix.mul_add, ← mul_kronecker_mul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.trace_add, trace_kronecker, htr, mul_one]
  congr 1; ring

/-! ### full pinching via random signs -/

variable (n) in
abbrev Sg := n → Bool

def sgn (θ : n → Bool) (i : n) : ℂ := if θ i then 1 else -1

lemma sgn_mul_self (θ : n → Bool) (i : n) : sgn θ i * sgn θ i = 1 := by
  unfold sgn; split_ifs <;> norm_num

lemma star_sgn (θ : n → Bool) (i : n) : star (sgn θ i) = sgn θ i := by
  unfold sgn; split_ifs <;> simp

def Cm : Matrix (n × Sg n) (n × Sg n) ℂ := diagonal (fun x => sgn x.2 x.1)

lemma Cm_unitary : (Cm : Matrix (n × Sg n) (n × Sg n) ℂ) ∈ unitary _ := by
  rw [Unitary.mem_iff]
  unfold Cm
  rw [Matrix.star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
    diagonal_mul_diagonal]
  constructor
  all_goals
    rw [← diagonal_one]; congr 1; ext x
    simp [star_sgn, sgn_mul_self]

lemma sum_sgn (i j : n) :
    ∑ θ : Sg n, sgn θ i * sgn θ j = if i = j then (Fintype.card (Sg n) : ℂ) else 0 := by
  split_ifs with h
  · subst h; simp [sgn_mul_self]
  · -- flipping the i-th sign is an involution changing the sign of each term
    set φ : Sg n ≃ Sg n :=
      { toFun := fun θ => Function.update θ i (!θ i)
        invFun := fun θ => Function.update θ i (!θ i)
        left_inv := fun θ => by ext k; by_cases hk : k = i <;> simp [Function.update, hk]
        right_inv := fun θ => by ext k; by_cases hk : k = i <;> simp [Function.update, hk] }
    have hs : ∑ θ : Sg n, sgn θ i * sgn θ j = ∑ θ : Sg n, sgn (φ θ) i * sgn (φ θ) j :=
      (Equiv.sum_comp φ _).symm
    have hneg : ∀ θ : Sg n, sgn (φ θ) i * sgn (φ θ) j = -(sgn θ i * sgn θ j) := by
      intro θ
      have h1 : (φ θ) i = !θ i := by simp [φ]
      have h2 : (φ θ) j = θ j := by simp [φ, Function.update, Ne.symm h]
      unfold sgn; rw [h1, h2]; cases θ i <;> cases θ j <;> simp
    rw [Finset.sum_congr rfl (fun θ _ => hneg θ), Finset.sum_neg_distrib] at hs
    have : (2 : ℂ) * ∑ θ : Sg n, sgn θ i * sgn θ j = 0 := by rw [two_mul]; nth_rewrite 2 [hs]; ring
    simpa using this

/-- the uniform mixing state on the sign register -/
noncomputable def tau : Matrix (Sg n) (Sg n) ℂ := ((Fintype.card (Sg n) : ℂ)⁻¹) • 1

lemma tau_posDef : (tau : Matrix (Sg n) (Sg n) ℂ).PosDef := by
  unfold tau
  have hc : (0 : ℝ) < (Fintype.card (Sg n) : ℝ)⁻¹ := by
    have : 0 < Fintype.card (Sg n) := Fintype.card_pos
    positivity
  have := (Matrix.PosDef.one (n := Sg n) (R := ℂ)).smul (a := ((Fintype.card (Sg n) : ℝ)⁻¹ : ℂ))
    (by exact_mod_cast hc)
  simpa using this

lemma tau_trace : (tau : Matrix (Sg n) (Sg n) ℂ).trace = 1 := by
  unfold tau
  rw [trace_smul, trace_one, smul_eq_mul]
  have : (Fintype.card (Sg n) : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_pos).ne'
  field_simp

noncomputable def pin (ρ : Matrix n n ℂ) : Matrix (n × Sg n) (n × Sg n) ℂ :=
  Cm * (ρ ⊗ₖ tau) * star Cm

lemma ptr_pin {n : Type} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ) :
    WildeQIT.partialTraceRight (pin ρ) = diagonal (fun i => ρ i i) := by
  ext i j
  simp only [WildeQIT.partialTraceRight, pin, Cm, tau, Matrix.of_apply, Matrix.star_eq_conjTranspose,
    diagonal_conjTranspose, mul_diagonal, diagonal_mul, kroneckerMap_apply, Matrix.smul_apply,
    Matrix.one_apply_eq, Pi.star_apply, star_sgn, smul_eq_mul, mul_one]
  have : ∀ k : Sg n, sgn k i * (ρ i j * (Fintype.card (Sg n) : ℂ)⁻¹) * sgn k j =
      (ρ i j * (Fintype.card (Sg n) : ℂ)⁻¹) * (sgn k i * sgn k j) := fun k => by ring
  rw [Finset.sum_congr rfl (fun k _ => this k), ← Finset.mul_sum, sum_sgn]
  have hc : (Fintype.card (Sg n) : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_pos).ne'
  by_cases h : i = j
  · subst h; simp [hc]
  · simp [h]

lemma pin_posDef {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) : (pin ρ).PosDef := by
  have hk : (ρ ⊗ₖ (tau : Matrix (Sg n) (Sg n) ℂ)).PosDef := hρ.kronecker tau_posDef
  have hU : IsUnit (Cm : Matrix (n × Sg n) (n × Sg n) ℂ) := by
    have h := (Unitary.mem_iff.1 (Cm_unitary (n := n))).2
    exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse h)
  unfold pin
  rw [Matrix.star_eq_conjTranspose]
  exact (hk.posSemidef.mul_mul_conjTranspose_same _).posDef_iff_isUnit.mpr
    ((hU.mul hk.isUnit).mul hU.star)

lemma pin_trace {ρ : Matrix n n ℂ} (htr : ρ.trace = 1) : (pin ρ).trace = 1 := by
  have hU : star (Cm : Matrix (n × Sg n) (n × Sg n) ℂ) * Cm = 1 :=
    (Unitary.mem_iff.1 (Cm_unitary (n := n))).1
  unfold pin
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, trace_kronecker, htr, tau_trace, one_mul]

/-- data processing for full pinching (dephasing in the standard basis) -/
theorem dpi_diag {H : Type} [Fintype H] [DecidableEq H] [Nonempty H] {ρ σ : Matrix H H ℂ}
    (hρ : QAlgorithms.IsDensityMatrix ρ) (hρ' : ρ.PosDef)
    (hσ : QAlgorithms.IsDensityMatrix σ) (hσ' : σ.PosDef) :
    relEntropy (diagonal (fun i => ρ i i)) (diagonal (fun i => σ i i)) ≤ relEntropy ρ σ := by
  have h := SimpleSSA.Monotone.eq_4 (pin ρ) (pin σ)
    ⟨(pin_posDef hρ').posSemidef, pin_trace hρ.2⟩ (pin_posDef hρ')
    ⟨(pin_posDef hσ').posSemidef, pin_trace hσ.2⟩ (pin_posDef hσ')
  rw [ptr_pin, ptr_pin, relEnt_eq, relEnt_eq] at h
  refine h.trans (le_of_eq ?_)
  unfold pin
  rw [relEnt_conj ⟨Cm, Cm_unitary⟩ (hρ'.kronecker tau_posDef).isHermitian
    (hσ'.kronecker tau_posDef).isHermitian, relEnt_kron hρ' hσ' tau_posDef tau_trace]

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

lemma logsum (S : Finset ι) (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) :
    (∑ i ∈ S, p i) * Real.log (∑ i ∈ S, p i) - (∑ i ∈ S, p i) * Real.log (∑ i ∈ S, q i) ≤
      ∑ i ∈ S, (p i * Real.log (p i) - p i * Real.log (q i)) := by
  set P := ∑ i ∈ S, p i
  set Q := ∑ i ∈ S, q i
  rcases (Finset.sum_nonneg (fun i (_ : i ∈ S) => hp i)).eq_or_lt with hP | hP
  · have h0 : ∀ i ∈ S, p i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hp i)).1 hP.symm
    have hr : ∑ i ∈ S, (p i * Real.log (p i) - p i * Real.log (q i)) = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [h0 i hi]; simp)
    have hP0 : P = 0 := hP.symm
    rw [hr, hP0]; simp
  have hS : S.Nonempty := by
    by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h; simp [P, h] at hP
  have hQ : 0 < Q := Finset.sum_pos (fun i _ => hq i) hS
  have key : ∀ i ∈ S, p i - q i * P / Q ≤
      (p i * Real.log (p i) - p i * Real.log (q i)) - (p i * Real.log P - p i * Real.log Q) := by
    intro i _
    rcases (hp i).eq_or_lt with h | h
    · rw [← h]; simp; exact div_nonneg (mul_nonneg (hq i).le hP.le) hQ.le
    have hx : 0 < q i * P / (p i * Q) := by have := hq i; positivity
    have hl := Real.log_le_sub_one_of_pos hx
    rw [Real.log_div (by have := hq i; positivity) (by positivity),
      Real.log_mul (hq i).ne' hP.ne', Real.log_mul h.ne' hQ.ne'] at hl
    have e : p i * (q i * P / (p i * Q) - 1) = q i * P / Q - p i := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hl h.le]
  have hsum := Finset.sum_le_sum key
  have e1 : ∑ x ∈ S, q x * P / Q = P := by
    rw [← Finset.sum_div, ← Finset.sum_mul]; exact mul_div_cancel_left₀ P hQ.ne'
  have e2 : ∑ x ∈ S, (p x * Real.log P - p x * Real.log Q) = P * Real.log P - P * Real.log Q := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, e1, e2] at hsum
  linarith

lemma kl_nonneg (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) (hsp : ∑ i, p i = 1)
    (hsq : ∑ i, q i = 1) : 0 ≤ ∑ i, (p i * Real.log (p i) - p i * Real.log (q i)) := by
  have := logsum Finset.univ p q hp hq
  rw [hsp, hsq] at this; simpa using this

lemma mlog_div (a b : ℝ) (hb : b ≠ 0) : a * Real.log (a / b) = a * Real.log a - a * Real.log b := by
  rcases eq_or_ne a 0 with h | h
  · subst h; simp
  rw [Real.log_div h hb]; ring

theorem pinsker_cl (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) (hsp : ∑ i, p i = 1)
    (hsq : ∑ i, q i = 1) :
    (∑ i, |p i - q i|) ^ 2 ≤ 2 * ∑ i, (p i * Real.log (p i) - p i * Real.log (q i)) := by
  classical
  set A := Finset.univ.filter (fun i => q i ≤ p i)
  set Ac := Finset.univ.filter (fun i => ¬ q i ≤ p i)
  set P := ∑ i ∈ A, p i
  set Q := ∑ i ∈ A, q i
  have hPc : ∑ i ∈ Ac, p i = 1 - P := by
    rw [← hsp, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => q i ≤ p i)]; ring
  have hQc : ∑ i ∈ Ac, q i = 1 - Q := by
    rw [← hsq, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => q i ≤ p i)]; ring
  have habs : ∑ i, |p i - q i| = 2 * (P - Q) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => q i ≤ p i)]
    rw [Finset.sum_congr rfl (fun i hi => abs_of_nonneg (sub_nonneg.2 (Finset.mem_filter.1 hi).2)),
      Finset.sum_congr rfl (fun i hi => abs_of_neg (sub_neg.2 (lt_of_not_ge
        (Finset.mem_filter.1 hi).2)))]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_sub_distrib]
    change (P - Q) + -(∑ i ∈ Ac, p i - ∑ i ∈ Ac, q i) = _
    rw [hPc, hQc]; ring
  have hKL := kl_nonneg p q hp hq hsp hsq
  have hsplit : ∑ i, (p i * Real.log (p i) - p i * Real.log (q i)) =
      ∑ i ∈ A, (p i * Real.log (p i) - p i * Real.log (q i)) +
        ∑ i ∈ Ac, (p i * Real.log (p i) - p i * Real.log (q i)) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have h1 := logsum A p q hp hq
  have h2 := logsum Ac p q hp hq
  rw [hPc, hQc] at h2
  rw [habs]
  have hPQ : Q ≤ P := Finset.sum_le_sum (fun i hi => (Finset.mem_filter.1 hi).2)
  have hP0 : 0 ≤ Q := Finset.sum_nonneg (fun i _ => (hq i).le)
  have hP1 : P ≤ 1 := by
    have : 0 ≤ ∑ i ∈ Ac, p i := Finset.sum_nonneg (fun i _ => hp i)
    linarith
  rcases hP0.eq_or_lt with hQ0 | hQ0
  · -- A is empty
    have hA : A = ∅ := by
      by_contra h
      have := Finset.sum_pos (fun i _ => hq i) (Finset.nonempty_iff_ne_empty.2 h)
      linarith
    have : P = 0 := by simp [P, hA]
    rw [this, ← hQ0]; nlinarith
  rcases (show Q ≤ 1 by linarith).eq_or_lt with hQ1 | hQ1
  · have : P = 1 := by linarith
    rw [this, hQ1]; nlinarith
  have hb := BanditAlgorithm.bernoulli_relative_entropy_pinsker P Q ⟨hQ0.le.trans hPQ, hP1⟩
    ⟨hQ0, hQ1⟩
  unfold BanditAlgorithm.bernoulliRelativeEntropy at hb
  rw [mlog_div _ _ hQ0.ne', mlog_div _ _ (by linarith)] at hb
  nlinarith

/-! ### quantum part -/

lemma relEnt_diag (p q : ι → ℝ) :
    relEntropy (diagonal (fun i => ((p i : ℝ) : ℂ))) (diagonal (fun i => ((q i : ℝ) : ℂ))) =
      ∑ i, (p i * Real.log (p i) - p i * Real.log (q i)) := by
  rw [relEnt_def, cfc_diag, cfc_diag, diagonal_mul_diagonal, diagonal_mul_diagonal,
    diagonal_sub, trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.sub_re, Complex.mul_re]

lemma traceNorm_herm {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    QAlgorithms.traceNorm M = ∑ i, |hM.eigenvalues i| := by
  unfold QAlgorithms.traceNorm
  have h1 : Mᴴ * M = cfc (fun x : ℝ => x * x) M := by
    rw [hM.eq, cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) M, cfc_id' ℝ M hM.isSelfAdjoint]
  have h2 : cfc Real.sqrt (Mᴴ * M) = cfc (fun x : ℝ => |x|) M := by
    rw [h1, ← cfc_comp Real.sqrt (fun x : ℝ => x * x) M]
    refine cfc_congr fun x _ => ?_
    simp [Real.sqrt_mul_self_eq_abs]
  rw [h2, X5AF.tr_cfc hM, Complex.re_sum]
  simp

lemma conj_posDef (U : unitary (Matrix ι ι ℂ)) {X : Matrix ι ι ℂ} (hX : X.PosDef) :
    ((U : Matrix ι ι ℂ) * X * star (U : Matrix ι ι ℂ)).PosDef := by
  have hU : IsUnit (U : Matrix ι ι ℂ) :=
    (Matrix.isUnit_iff_isUnit_det _).2
      (Matrix.isUnit_det_of_right_inverse (Unitary.mul_star_self_of_mem U.2))
  rw [Matrix.star_eq_conjTranspose]
  exact (hX.posSemidef.mul_mul_conjTranspose_same _).posDef_iff_isUnit.mpr
    ((hU.mul hX.isUnit).mul hU.star)

lemma conj_trace (U : unitary (Matrix ι ι ℂ)) (X : Matrix ι ι ℂ) :
    ((U : Matrix ι ι ℂ) * X * star (U : Matrix ι ι ℂ)).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, Unitary.star_mul_self_of_mem U.2, Matrix.one_mul]

/-- quantum Pinsker inequality for invertible states, ground universe -/
theorem pinsker_pd0 {H : Type} [Fintype H] [DecidableEq H] [Nonempty H] {ρ σ : Matrix H H ℂ}
    (hρ : QAlgorithms.IsDensityMatrix ρ) (hρ' : ρ.PosDef)
    (hσ : QAlgorithms.IsDensityMatrix σ) (hσ' : σ.PosDef) :
    QAlgorithms.traceNorm (ρ - σ) ^ 2 ≤ 2 * relEntropy ρ σ := by
  have hM : (ρ - σ).IsHermitian := hρ'.isHermitian.sub hσ'.isHermitian
  set W : unitary (Matrix H H ℂ) := star hM.eigenvectorUnitary
  set ρ' := (W : Matrix H H ℂ) * ρ * star (W : Matrix H H ℂ)
  set σ' := (W : Matrix H H ℂ) * σ * star (W : Matrix H H ℂ)
  have hρ'' : ρ'.PosDef := conj_posDef W hρ'
  have hσ'' : σ'.PosDef := conj_posDef W hσ'
  have hd := dpi_diag (ρ := ρ') (σ := σ') ⟨hρ''.posSemidef, (conj_trace W ρ).trans hρ.2⟩ hρ''
    ⟨hσ''.posSemidef, (conj_trace W σ).trans hσ.2⟩ hσ''
  rw [relEnt_conj W hρ'.isHermitian hσ'.isHermitian] at hd
  set p : H → ℝ := fun i => (ρ' i i).re
  set q : H → ℝ := fun i => (σ' i i).re
  have ep : (diagonal fun i => ρ' i i) = diagonal (fun i => ((p i : ℝ) : ℂ)) := by
    congr 1; ext i; exact (hρ''.isHermitian.coe_re_apply_self i).symm
  have eq' : (diagonal fun i => σ' i i) = diagonal (fun i => ((q i : ℝ) : ℂ)) := by
    congr 1; ext i; exact (hσ''.isHermitian.coe_re_apply_self i).symm
  rw [ep, eq', relEnt_diag] at hd
  have hp : ∀ i, 0 ≤ p i := fun i => by
    have := hρ''.posSemidef.diag_nonneg (i := i)
    exact (Complex.nonneg_iff.1 this).1
  have hq : ∀ i, 0 < q i := fun i => by
    have := hσ''.diag_pos (i := i)
    exact (Complex.pos_iff.1 this).1
  have hsum : ∀ X : Matrix H H ℂ, X.trace = 1 → ∑ i, (X i i).re = 1 := fun X h => by
    rw [← Complex.re_sum]; change (X.trace).re = 1; rw [h]; simp
  have hsp := hsum ρ' ((conj_trace W ρ).trans hρ.2)
  have hsq := hsum σ' ((conj_trace W σ).trans hσ.2)
  have hcl := pinsker_cl p q hp hq hsp hsq
  -- p - q are the eigenvalues of ρ - σ
  have hdiag : ρ' - σ' = diagonal (fun i => ((hM.eigenvalues i : ℝ) : ℂ)) := by
    have hs := hM.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at hs
    simp only [ρ', σ']
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    exact hs
  have hpq : ∀ i, p i - q i = hM.eigenvalues i := fun i => by
    have := congrArg (fun X => (X i i).re) hdiag
    simpa [p, q] using this
  rw [traceNorm_herm hM, ← Finset.sum_congr rfl (fun i _ => congrArg abs (hpq i))]
  linarith

theorem pinsker_pd {H : Type*} [Fintype H] [DecidableEq H] [Nonempty H] {ρ σ : Matrix H H ℂ}
    (hρ : QAlgorithms.IsDensityMatrix ρ) (hρ' : ρ.PosDef)
    (hσ : QAlgorithms.IsDensityMatrix σ) (hσ' : σ.PosDef) :
    QAlgorithms.traceNorm (ρ - σ) ^ 2 ≤ 2 * relEntropy ρ σ := by
  set e : Fin (Fintype.card H) ≃ H := (Fintype.equivFin H).symm
  haveI : Nonempty (Fin (Fintype.card H)) := ⟨⟨0, Fintype.card_pos⟩⟩
  have h := pinsker_pd0 (X5AF.dens_sub hρ e) (hρ'.submatrix e.injective)
    (X5AF.dens_sub hσ e) (hσ'.submatrix e.injective)
  have h2 : ρ.submatrix e e - σ.submatrix e e = (ρ - σ).submatrix e e := by ext; simp
  rw [relEnt_sub hρ'.isHermitian hσ'.isHermitian, h2, X5AF.traceNorm_sub] at h
  exact h

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

lemma traceNorm_rsmul (a : ℝ) (ha : 0 ≤ a) (M : Matrix ι ι ℂ) :
    QAlgorithms.traceNorm (((a : ℝ) : ℂ) • M) = a * QAlgorithms.traceNorm M := by
  unfold QAlgorithms.traceNorm
  have hZ : (Mᴴ * M).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  have e : (((a : ℝ) : ℂ) • M)ᴴ * (((a : ℝ) : ℂ) • M) = ((a ^ 2 : ℝ) : ℂ) • (Mᴴ * M) := by
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1; simp [Complex.conj_ofReal]; ring
  rw [e, real_smul, ← cfc_comp_smul (a ^ 2) Real.sqrt (Mᴴ * M) Real.continuous_sqrt.continuousOn hZ.isSelfAdjoint]
  have : cfc (fun x => Real.sqrt (a ^ 2 • x)) (Mᴴ * M) = a • cfc Real.sqrt (Mᴴ * M) := by
    rw [← cfc_smul a Real.sqrt (Mᴴ * M) (X5B2.fin _ _)]
    refine cfc_congr fun x _ => ?_
    simp only [smul_eq_mul]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ha]
  rw [this, trace_smul]
  simp [Complex.real_smul]

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


noncomputable def pert (d ε : ℝ) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (((1 - ε : ℝ)) : ℂ) • X + ((ε / d : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)

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

/-- quantum Pinsker inequality under the support condition `ker σ ⊆ ker ρ` -/
theorem pinsker_ker {H : Type*} [Fintype H] [DecidableEq H] [Nonempty H] {ρ σ : Matrix H H ℂ}
    (hρ : QAlgorithms.IsDensityMatrix ρ) (hσ : QAlgorithms.IsDensityMatrix σ)
    (hker : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin) :
    QAlgorithms.traceNorm (ρ - σ) ^ 2 ≤ 2 * relEntropy ρ σ := by
  set d : ℝ := (Fintype.card H : ℝ)
  have hd : 0 < d := by simp only [d]; exact_mod_cast Fintype.card_pos (α := H)
  have hρH := hρ.1.isHermitian
  have hσH := hσ.1.isHermitian
  set U := (hσH.eigenvectorUnitary : Matrix H H ℂ)
  set s := hσH.eigenvalues
  set l := hρH.eigenvalues
  set r : H → ℝ := fun j => ((star U * ρ * U) j j).re
  let F : ℝ → ℝ := fun ε =>
    (∑ i, ((1 - ε) * l i + ε / d) * Real.log ((1 - ε) * l i + ε / d)) -
      ∑ j, ((1 - ε) * r j + ε / d) * Real.log ((1 - ε) * s j + ε / d)
  -- Claim A
  have hA : ∀ ε : ℝ, relEntropy (pert d ε ρ) (pert d ε σ) = F ε := by
    intro ε
    have h1 := aff_herm hρH (1 - ε) (ε / d)
    rw [relEnt_def, Matrix.trace_sub, Complex.sub_re]
    unfold pert
    rw [mul_log _ h1, cfc_aff hρH, cfc_aff hσH, X5AF.tr_cfc hρH, Complex.re_sum,
      tr_mul_cfc h1 hσH]
    simp only [Complex.ofReal_re]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Unitary.star_mul_self_of_mem hσH.eigenvectorUnitary.2]
    simp [r, Complex.mul_re]
    left; rfl
  -- support facts
  have hsd : star U * σ * U = diagonal (fun j => ((s j : ℝ) : ℂ)) := by
    have hs := hσH.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at hs
    simp only [Unitary.coe_star, star_star] at hs
    exact hs
  have hs0 : ∀ j, 0 ≤ s j := fun j => hσ.1.eigenvalues_nonneg j
  have hr0 : ∀ j, 0 ≤ r j := fun j => by
    have h := (hρ.1.conjTranspose_mul_mul_same U).diag_nonneg (i := j)
    rw [← Matrix.star_eq_conjTranspose] at h
    exact (Complex.nonneg_iff.1 h).1
  have hrs : ∀ j, s j = 0 → r j = 0 := fun j hj => by
    have hV : (Uᴴ)ᴴ * Uᴴ = 1 := by
      rw [conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose]
      exact Unitary.mul_star_self_of_mem hσH.eigenvectorUnitary.2
    have hk := ker_conj' hV hker
    rw [conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose, hsd] at hk
    have := ker_single hk (fun a b hab => by simp [hab]) j (by simp [hj])
    simp [r, this]
  -- Claim B: continuity of F at 0
  have hB : ContinuousAt F 0 := by
    have c1 : ∀ i, ContinuousAt (fun ε : ℝ => ((1 - ε) * l i + ε / d) *
        Real.log ((1 - ε) * l i + ε / d)) 0 := fun i =>
      (Real.continuous_mul_log.comp (by fun_prop : Continuous fun ε : ℝ =>
        (1 - ε) * l i + ε / d)).continuousAt
    have c2 : ∀ j, ContinuousAt (fun ε : ℝ => ((1 - ε) * r j + ε / d) *
        Real.log ((1 - ε) * s j + ε / d)) 0 := fun j => by
      rcases (hs0 j).eq_or_lt with h | h
      · have hr := hrs j h.symm
        rw [hr, ← h]
        simp only [mul_zero, zero_add]
        exact (Real.continuous_mul_log.comp (by fun_prop : Continuous fun ε : ℝ =>
          ε / d)).continuousAt
      · refine ContinuousAt.mul (by fun_prop) (ContinuousAt.log (by fun_prop) ?_)
        simp; exact h.ne'
    exact (tendsto_finsetSum _ (fun i _ => c1 i)).sub (tendsto_finsetSum _ (fun j _ => c2 j))
  -- Claim C
  have hC : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ((1 - ε) * QAlgorithms.traceNorm (ρ - σ)) ^ 2 ≤ 2 * F ε := by
    intro ε hε
    have ha : (0 : ℝ) ≤ 1 - ε := by linarith [hε.2]
    have hb : 0 < ε / d := div_pos hε.1 hd
    have hpd : ∀ X : Matrix H H ℂ, QAlgorithms.IsDensityMatrix X →
        QAlgorithms.IsDensityMatrix (pert d ε X) ∧ (pert d ε X).PosDef := by
      intro X hX
      have hp : (pert d ε X).PosDef := by
        unfold pert
        refine Matrix.PosDef.posSemidef_add (hX.1.smul (by exact_mod_cast ha)) ?_
        have := (Matrix.PosDef.one (n := H) (R := ℂ)).smul (a := ((ε / d : ℝ) : ℂ))
          (by exact_mod_cast hb)
        exact this
      refine ⟨⟨hp.posSemidef, ?_⟩, hp⟩
      unfold pert
      rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hX.2, Matrix.trace_one]
      simp only [smul_eq_mul, mul_one]
      push_cast
      field_simp
      simp only [d]; push_cast; ring
    obtain ⟨h1, h2⟩ := hpd ρ hρ
    obtain ⟨h3, h4⟩ := hpd σ hσ
    have hp := pinsker_pd h1 h2 h3 h4
    have e : pert d ε ρ - pert d ε σ = (((1 - ε : ℝ)) : ℂ) • (ρ - σ) := by
      unfold pert; rw [add_sub_add_right_eq_sub, ← smul_sub]
    rw [e, traceNorm_rsmul _ ha, hA] at hp
    exact hp
  -- Claim D
  have hD : F 0 = relEntropy ρ σ := by
    rw [← hA 0]; unfold pert; simp
  -- limit
  have t1 : Tendsto (fun ε : ℝ => ((1 - ε) * QAlgorithms.traceNorm (ρ - σ)) ^ 2) (𝓝[>] 0)
      (𝓝 (QAlgorithms.traceNorm (ρ - σ) ^ 2)) := by
    have : Continuous (fun ε : ℝ => ((1 - ε) * QAlgorithms.traceNorm (ρ - σ)) ^ 2) := by fun_prop
    have h := this.tendsto 0
    simp only [sub_zero, one_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have t2 : Tendsto (fun ε => 2 * F ε) (𝓝[>] 0) (𝓝 (2 * relEntropy ρ σ)) := by
    rw [← hD]; exact (hB.const_mul 2).tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto t1 t2
    (Filter.mem_of_superset (Ioo_mem_nhdsGT one_pos) fun ε hε => hC ε hε)

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

end

variable {H : Type} [Fintype H] [DecidableEq H]

end X5PK
end X5mod_PK_Add

section X5mod_PR_Main
open Matrix Finset Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PR
open X5QC X5PK
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Re Tr (σ supp τ) = Re Tr σ` when `ker τ ⊆ ker σ` -/
lemma tr_supp {σ τ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) (hτ : τ.PosSemidef)
    (hker : LinearMap.ker τ.mulVecLin ≤ LinearMap.ker σ.mulVecLin) :
    (σ * supp τ).trace.re = σ.trace.re := by
  set V := (hτ.1.eigenvectorUnitary : Matrix ι ι ℂ)
  set s := hτ.1.eigenvalues
  set w : ι → ℝ := fun j => ((star V * σ * V) j j).re
  have h1 := tr_mul_cfc hσ.1 hτ.1 ind
  have h2 := tr_mul_cfc hσ.1 hτ.1 (fun _ => 1)
  rw [cfc_const_one ℝ τ, Matrix.mul_one] at h2
  change (σ * supp τ).trace.re = ∑ j, w j * ind (s j) at h1
  change σ.trace.re = ∑ j, w j * 1 at h2
  have hsd : star V * τ * V = diagonal (fun j => ((s j : ℝ) : ℂ)) := by
    have hs := hτ.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at hs
    simp only [Unitary.coe_star, star_star] at hs
    exact hs
  have hsupp : ∀ j, s j = 0 → w j = 0 := fun j hj => by
    have hV : (Vᴴ)ᴴ * Vᴴ = 1 := by
      rw [conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose]
      exact Unitary.mul_star_self_of_mem hτ.1.eigenvectorUnitary.2
    have hk := ker_conj' hV hker
    rw [conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose, hsd] at hk
    have := ker_single hk (fun a b hab => by simp [hab]) j (by simp [hj])
    simp [w, this]
  rw [h1, h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : s j = 0
  · simp [hsupp j hj]
  · simp [ind, hj]

/-- `Re Tr (σ log (c τ)) = log c · Re Tr σ + Re Tr (σ log τ)` when `ker τ ⊆ ker σ` -/
lemma tr_log_smul {σ τ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) (hτ : τ.PosSemidef)
    (hker : LinearMap.ker τ.mulVecLin ≤ LinearMap.ker σ.mulVecLin) {c : ℝ} (hc : 0 < c) :
    (σ * cfc Real.log ((c : ℂ) • τ)).trace.re =
      Real.log c * σ.trace.re + (σ * cfc Real.log τ).trace.re := by
  rw [cfc_log_smul hc τ hτ.1, Matrix.mul_add, Matrix.trace_add, Complex.add_re, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, tr_supp hσ hτ hker]

section
variable {L H : Type*} [Fintype L] [DecidableEq L] [Fintype H] [DecidableEq H]

lemma tr_mul_bd (X : Matrix (L × H) (L × H) ℂ) (W : L → Matrix H H ℂ) :
    (X * bd W).trace = ∑ a, (Matrix.of (fun s t => X (a, s) (a, t)) * W a).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, bd, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma bd_mulVec (W : L → Matrix H H ℂ) (v : L × H → ℂ) (a : L) (s : H) :
    (bd W *ᵥ v) (a, s) = (W a *ᵥ (fun t => v (a, t))) s := by
  simp only [Matrix.mulVec, dotProduct, bd, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp
end

section priv
open QAlgorithms.Papers.Independent.Dependency50.P24
variable {d : ℕ} [NeZero d] {H : Type*} [Fintype H] [DecidableEq H]

/-- isometry `H → Key d × H` with `privateMatrix τ U = M τ Mᴴ` -/
noncomputable def isoM (U : Fin d → Matrix.unitaryGroup H ℂ) : Matrix (Key d × H) H ℂ :=
  fun a t => if a.1.1 = a.1.2 then ((Real.sqrt d)⁻¹ : ℂ) * (U a.1.1 : Matrix H H ℂ) a.2 t else 0

lemma isoM_ct_mul (U : Fin d → Matrix.unitaryGroup H ℂ) : (isoM U)ᴴ * isoM U = 1 := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  ext s t
  simp only [isoM, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  have e : ∀ (i j : Fin d) (u : H), star (if i = j then ((Real.sqrt d)⁻¹ : ℂ) *
      (U i : Matrix H H ℂ) u s else 0) * (if i = j then ((Real.sqrt d)⁻¹ : ℂ) *
      (U i : Matrix H H ℂ) u t else 0) =
      if i = j then ((d : ℝ)⁻¹ : ℂ) * (star ((U i : Matrix H H ℂ) u s) *
        (U i : Matrix H H ℂ) u t) else 0 := by
    intro i j u
    split_ifs
    · have h2 : ((Real.sqrt d)⁻¹ : ℂ) * ((Real.sqrt d)⁻¹ : ℂ) = ((d : ℝ)⁻¹ : ℂ) := by
        rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hd.le]
      simp only [star_mul', Complex.star_def, map_inv₀, Complex.conj_ofReal]
      rw [← h2]; ring
    · simp
  simp only [e]
  have e2 : ∀ i : Fin d, ∑ j : Fin d, ∑ u : H, (if i = j then ((d : ℝ)⁻¹ : ℂ) *
      (star ((U i : Matrix H H ℂ) u s) * (U i : Matrix H H ℂ) u t) else 0) =
      ((d : ℝ)⁻¹ : ℂ) * (1 : Matrix H H ℂ) s t := by
    intro i
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
    simp only [if_true]
    rw [← Finset.mul_sum]
    congr 1
    have hU : star (U i : Matrix H H ℂ) * (U i : Matrix H H ℂ) = 1 :=
      Unitary.star_mul_self_of_mem (U i).2
    rw [← hU, Matrix.mul_apply]
    simp [Matrix.star_apply]
  simp only [e2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, Complex.ofReal_natCast, mul_inv_cancel₀ (by exact_mod_cast hd.ne'), one_mul]

lemma priv_eq (τ : Matrix H H ℂ) (U : Fin d → Matrix.unitaryGroup H ℂ) :
    privateMatrix τ U = isoM U * τ * (isoM U)ᴴ := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  ext a b
  simp only [privateMatrix, isoM, Matrix.mul_apply, Matrix.conjTranspose_apply]
  by_cases ha : a.1.1 = a.1.2 <;> by_cases hb : b.1.1 = b.1.2
  · simp only [ha, hb, and_self, if_true, star_mul', Complex.star_def, map_inv₀, Complex.conj_ofReal]
    have h2 : ((Real.sqrt d)⁻¹ : ℂ) * ((Real.sqrt d)⁻¹ : ℂ) = (d : ℂ)⁻¹ := by
      rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hd.le, Complex.ofReal_natCast]
    rw [← h2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    ring
  · simp [ha, hb]
  · simp [ha, hb]
  · simp [ha, hb]

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

lemma T_priv {τ : Matrix H H ℂ} (hτ : τ.PosSemidef) (U : Fin d → Matrix.unitaryGroup H ℂ) :
    T (privateMatrix τ U) = T τ := by
  rw [priv_eq]; exact T_iso hτ _ (isoM_ct_mul U)

lemma T_conj {τ : Matrix H H ℂ} (hτ : τ.PosSemidef) (V : Matrix.unitaryGroup H ℂ) :
    T ((V : Matrix H H ℂ) * τ * (V : Matrix H H ℂ)ᴴ) = T τ := by
  refine T_iso hτ _ ?_
  rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem V.2

lemma shield_eq (τ : Matrix H H ℂ) (U : Fin d → Matrix.unitaryGroup H ℂ) (i : Fin d) :
    conditionalShield (privateMatrix τ U) i =
      (U i : Matrix H H ℂ) * τ * (U i : Matrix H H ℂ)ᴴ := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  ext s t
  simp [conditionalShield, keyBlock, privateMatrix, hd]

lemma block_priv (τ : Matrix H H ℂ) (U : Fin d → Matrix.unitaryGroup H ℂ) (a : Key d) :
    Matrix.of (fun s t => privateMatrix τ U (a, s) (a, t)) =
      if a.1 = a.2 then (((d : ℝ)⁻¹ : ℝ) : ℂ) • ((U a.1 : Matrix H H ℂ) * τ * (U a.1 : Matrix H H ℂ)ᴴ)
      else 0 := by
  ext s t
  by_cases h : a.1 = a.2 <;> simp [privateMatrix, h]

/-- the separable reference built from shield references `τs` -/
noncomputable def omg (τs : Fin d → Matrix H H ℂ) : Matrix (Key d × H) (Key d × H) ℂ :=
  bd (fun a : Key d => if a.1 = a.2 then (((d : ℝ)⁻¹ : ℝ) : ℂ) • τs a.1 else 0)

lemma ker_omg {τ : Matrix H H ℂ} (U : Fin d → Matrix.unitaryGroup H ℂ) {τs : Fin d → Matrix H H ℂ}
    (hker : ∀ i, LinearMap.ker (τs i).mulVecLin ≤
      LinearMap.ker ((U i : Matrix H H ℂ) * τ * (U i : Matrix H H ℂ)ᴴ).mulVecLin) :
    LinearMap.ker (omg τs).mulVecLin ≤ LinearMap.ker (privateMatrix τ U).mulVecLin := by
  have hd : (((d : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
    exact_mod_cast inv_ne_zero this
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  -- blockwise kernel
  set w : Fin d → H → ℂ := fun i s => v ((i, i), s)
  have hw : ∀ i, τ *ᵥ ((U i : Matrix H H ℂ)ᴴ *ᵥ w i) = 0 := by
    intro i
    have h1 : τs i *ᵥ w i = 0 := by
      ext s
      have := congrFun hv ((i, i), s)
      rw [omg, bd_mulVec] at this
      simp only [if_true, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      exact (mul_eq_zero.1 this).resolve_left hd
    have h2 := hker i (show w i ∈ LinearMap.ker (τs i).mulVecLin by simpa using h1)
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h2
    have h3 := congrArg (fun x => (U i : Matrix H H ℂ)ᴴ *ᵥ x) h2
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h3
    have hU : (U i : Matrix H H ℂ)ᴴ * (U i : Matrix H H ℂ) = 1 := by
      rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem (U i).2
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul, ← Matrix.mulVec_mulVec] at h3
    exact h3
  have hMv : (isoM U)ᴴ *ᵥ v = ((Real.sqrt d)⁻¹ : ℂ) • ∑ j, (U j : Matrix H H ℂ)ᴴ *ᵥ w j := by
    ext u
    simp only [Matrix.mulVec, dotProduct, isoM, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum, w]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [Complex.conj_ofReal]; ring
  rw [priv_eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_smul,
    Matrix.mulVec_sum]
  simp [hw]

lemma R_priv {τ : Matrix H H ℂ} (hτ : QAlgorithms.IsDensityMatrix τ)
    (U : Fin d → Matrix.unitaryGroup H ℂ) {τs : Fin d → Matrix H H ℂ}
    (hτs : ∀ i, (τs i).PosSemidef)
    (hker : ∀ i, LinearMap.ker (τs i).mulVecLin ≤
      LinearMap.ker ((U i : Matrix H H ℂ) * τ * (U i : Matrix H H ℂ)ᴴ).mulVecLin) :
    T (privateMatrix τ U) - (privateMatrix τ U * cfc Real.log (omg τs)).trace.re =
      Real.log d + (d : ℝ)⁻¹ * ∑ i, (T ((U i : Matrix H H ℂ) * τ * (U i : Matrix H H ℂ)ᴴ) -
        ((U i : Matrix H H ℂ) * τ * (U i : Matrix H H ℂ)ᴴ * cfc Real.log (τs i)).trace.re) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  set σ : Fin d → Matrix H H ℂ := fun i => (U i : Matrix H H ℂ) * τ * (U i : Matrix H H ℂ)ᴴ
  have hσ : ∀ i, (σ i).PosSemidef := fun i => hτ.1.mul_mul_conjTranspose_same _
  have hσtr : ∀ i, (σ i).trace.re = 1 := fun i => by
    have hU : (U i : Matrix H H ℂ)ᴴ * (U i : Matrix H H ℂ) = 1 := by
      rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem (U i).2
    simp only [σ]; rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, hτ.2]; simp
  have hW : ∀ a : Key d, (if a.1 = a.2 then (((d : ℝ)⁻¹ : ℝ) : ℂ) • τs a.1 else 0).IsHermitian :=
    fun a => by
      split_ifs
      · exact ((hτs a.1).smul (a := (((d : ℝ)⁻¹ : ℝ) : ℂ)) (by exact_mod_cast (inv_nonneg.2 hd.le))).1
      · exact Matrix.isHermitian_zero
  have hc : (0 : ℝ) < (d : ℝ)⁻¹ := inv_pos.2 hd
  have inner : ∀ i : Fin d, ∑ j : Fin d, ((Matrix.of (fun s t => privateMatrix τ U ((i, j), s) ((i, j), t)) *
      cfc Real.log (if ((i, j) : Key d).1 = ((i, j) : Key d).2 then (((d : ℝ)⁻¹ : ℝ) : ℂ) • τs (i, j).1
        else 0)).trace).re =
      (d : ℝ)⁻¹ * (Real.log ((d : ℝ)⁻¹) + (σ i * cfc Real.log (τs i)).trace.re) := by
    intro i
    rw [Finset.sum_eq_single i]
    · have := block_priv τ U (i, i)
      simp only at this
      simp only [this, if_true]
      rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
        tr_log_smul (hσ i) (hτs i) (hker i) hc, hσtr i, mul_one]
    · intro j _ hj
      have := block_priv τ U (i, j)
      simp only at this
      simp [this, Ne.symm hj]
    · simp
  rw [omg, cfc_bd hW, tr_mul_bd, Complex.re_sum, Fintype.sum_prod_type]
  simp only [inner]
  rw [T_priv hτ.1]
  simp only [σ] at *
  simp only [T_conj hτ.1, Real.log_inv, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_add, mul_sub, Finset.sum_add_distrib]
  field_simp
  ring

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

/-- the reindexing behind `partyCut` -/
def pcE : (Fin d × S) × (Fin d × T') ≃ Key d × (S × T') where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun y := ((y.1.1, y.2.1), (y.1.2, y.2.2))
  left_inv x := rfl
  right_inv y := rfl

lemma partyCut_eq (X : Matrix (Key d × (S × T')) (Key d × (S × T')) ℂ) :
    partyCut X = X.submatrix pcE pcE := rfl

lemma ker_sub {m n : Type*} [Fintype m] [Fintype n] (e : n ≃ m) {M N : Matrix m m ℂ}
    (h : LinearMap.ker M.mulVecLin ≤ LinearMap.ker N.mulVecLin) :
    LinearMap.ker (M.submatrix e e).mulVecLin ≤ LinearMap.ker (N.submatrix e e).mulVecLin := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  have key : ∀ P : Matrix m m ℂ, P.submatrix e e *ᵥ v = fun x => (P *ᵥ (v ∘ e.symm)) (e x) := by
    intro P; ext x
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Function.comp]
    exact (Equiv.sum_comp e.symm _).symm.trans (by simp)
  rw [key] at hv ⊢
  have h0 : M *ᵥ (v ∘ e.symm) = 0 := by
    ext y; have := congrFun hv (e.symm y); simpa using this
  have := h (show v ∘ e.symm ∈ LinearMap.ker M.mulVecLin by simpa using h0)
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at this
  rw [this]; rfl

lemma omg_dens {H : Type*} [Fintype H] [DecidableEq H] {τs : Fin d → Matrix H H ℂ}
    (hτs : ∀ i, QAlgorithms.IsDensityMatrix (τs i)) : QAlgorithms.IsDensityMatrix (omg τs) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  refine ⟨bd_psd fun a => ?_, ?_⟩
  · split_ifs
    · exact (hτs a.1).1.smul (by exact_mod_cast (inv_nonneg.2 hd.le))
    · exact Matrix.PosSemidef.zero
  · rw [omg, bd_trace, Fintype.sum_prod_type]
    have : ∀ i : Fin d, ∑ j : Fin d, (if ((i, j) : Key d).1 = ((i, j) : Key d).2 then
        (((d : ℝ)⁻¹ : ℝ) : ℂ) • τs (i, j).1 else 0).trace = (((d : ℝ)⁻¹ : ℝ) : ℂ) := by
      intro i
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
      simp [(hτs i).2]
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp

/-- key projector -/
def kp (i : Fin d) : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal fun k => if k = i then 1 else 0

lemma kp_dens (i : Fin d) : QAlgorithms.IsDensityMatrix (kp i) := by
  refine ⟨Matrix.posSemidef_diagonal_iff.2 fun k => by split_ifs <;> simp, ?_⟩
  simp [kp, Matrix.trace_diagonal]

lemma omg_sep [Nonempty S] [Nonempty T'] {τs : Fin d → Matrix (S × T') (S × T') ℂ}
    (hsep : ∀ i, QAlgorithms.Entanglement.IsSeparableDensity (τs i)) :
    QAlgorithms.Entanglement.IsSeparableDensity ((omg τs).submatrix pcE pcE) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  choose q w A B hw0 hw1 hAB hτ using hsep
  set c : (Σ i, Fin (q i)) → ℝ := fun k => (d : ℝ)⁻¹ * w k.1 k.2
  have e : (omg τs).submatrix pcE pcE = ∑ k : (Σ i, Fin (q i)), (c k : ℂ) •
      Matrix.kronecker (Matrix.kronecker (kp k.1) (A k.1 k.2)) (Matrix.kronecker (kp k.1) (B k.1 k.2)) := by
    ext x y
    rcases x with ⟨⟨i1, s1⟩, ⟨j1, t1⟩⟩
    rcases y with ⟨⟨i2, s2⟩, ⟨j2, t2⟩⟩
    simp only [Matrix.submatrix_apply, pcE, Equiv.coe_fn_mk, omg, bd, Matrix.sum_apply,
      Fintype.sum_sigma, Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.kronecker, kp,
      Matrix.diagonal_apply, c, smul_eq_mul]
    by_cases h1 : i1 = i2 <;> by_cases h2 : j1 = j2 <;> by_cases h3 : i1 = j1
    · subst h1 h2 h3
      rw [Finset.sum_eq_single i1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp only [Prod.mk.injEq, and_self, if_true, Matrix.smul_apply, smul_eq_mul, hτ i1,
        Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
      push_cast; ring
    all_goals
      refine Eq.trans (b := (0 : ℂ)) ?_ ?_
      · simp_all
      · refine (Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun j _ => ?_).symm
        by_cases hb : i1 = b <;> by_cases hb' : j1 = b <;> simp_all
  rw [e]
  refine sep_of_sum c _ _ (fun k => mul_nonneg (inv_nonneg.2 hd.le) (hw0 k.1 k.2)) ?_ fun k => ?_
  · simp only [c, Fintype.sum_sigma, ← Finset.mul_sum, hw1, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
  · obtain ⟨hA, hB⟩ := hAB k.1 k.2
    refine ⟨⟨(kp_dens k.1).1.kronecker hA.1, ?_⟩, ⟨(kp_dens k.1).1.kronecker hB.1, ?_⟩⟩
    · erw [Matrix.trace_kronecker, (kp_dens k.1).2, hA.2, one_mul]
    · erw [Matrix.trace_kronecker, (kp_dens k.1).2, hB.2, one_mul]

end final

section bits
open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma sep_dens {J K : Type*} [Fintype J] [Fintype K] [Nonempty J] [Nonempty K] [DecidableEq J]
    [DecidableEq K] {X : Matrix (J × K) (J × K) ℂ}
    (h : QAlgorithms.Entanglement.IsSeparableDensity X) : QAlgorithms.IsDensityMatrix X := by
  obtain ⟨q, w, A, B, hw0, hw1, hAB, rfl⟩ := h
  refine ⟨Matrix.posSemidef_sum _ fun j _ => ((hAB j).1.1.kronecker (hAB j).2.1).smul
    (by exact_mod_cast hw0 j), ?_⟩
  rw [Matrix.trace_sum]
  have : ∀ j, ((w j : ℂ) • Matrix.kronecker (A j) (B j)).trace = (w j : ℂ) := fun j => by
    rw [Matrix.trace_smul]; erw [Matrix.trace_kronecker, (hAB j).1.2, (hAB j).2.2]; simp
  simp only [this]; exact_mod_cast hw1

lemma relEnt_nonneg [Nonempty I] {ρ σ : Matrix I I ℂ} (hρ : QAlgorithms.IsDensityMatrix ρ)
    (hσ : QAlgorithms.IsDensityMatrix σ)
    (hker : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin) : 0 ≤ X5PK.relEntropy ρ σ := by
  have := pinsker_ker hρ hσ hker
  nlinarith [sq_nonneg (QAlgorithms.traceNorm (ρ - σ))]

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

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Finset
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)
open QAlgorithms.Papers.Independent.Dependency50.P24

theorem solution {d : ℕ} [NeZero d] {S T : Type*}
    [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (gamma : Op (Key d × (S × T))) (hgamma : IsPrivate gamma) :
    relativeEntanglement (partyCut gamma) ≤ ENNReal.ofReal (logBits d) +
      (d : ℝ≥0∞)⁻¹ * ∑ i, relativeEntanglement (conditionalShield gamma i) := by
  obtain ⟨hγ, τ, hτ, U, rfl⟩ := hgamma
  simp only [X5PR.shield_eq]
  set σ : Fin d → Matrix (S × T) (S × T) ℂ :=
    fun i => (U i : Matrix (S × T) (S × T) ℂ) * τ * (U i : Matrix (S × T) (S × T) ℂ)ᴴ with hσdef
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hdE : (d : ℝ≥0∞) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hσd : ∀ i, QAlgorithms.IsDensityMatrix (σ i) := fun i => by
    refine ⟨hτ.1.mul_mul_conjTranspose_same _, ?_⟩
    have hU : (U i : Matrix (S × T) (S × T) ℂ)ᴴ * (U i : Matrix (S × T) (S × T) ℂ) = 1 := by
      rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem (U i).2
    simp only [σ]; rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, hτ.2]
  by_cases htop : ∃ i, relativeEntanglement (σ i) = ⊤
  · obtain ⟨i, hi⟩ := htop
    have : (d : ℝ≥0∞)⁻¹ * ∑ i, relativeEntanglement (σ i) = ⊤ := by
      rw [ENNReal.mul_eq_top]
      exact Or.inl ⟨by simp, ENNReal.sum_eq_top.2 ⟨i, Finset.mem_univ _, hi⟩⟩
    rw [this, add_top]; exact le_top
  push_neg at htop
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hch : ∀ i, ∃ τi : Matrix (S × T) (S × T) ℂ, QAlgorithms.Entanglement.IsSeparableDensity τi ∧
      relativeEntropyBits (σ i) τi < relativeEntanglement (σ i) + ε := by
    intro i
    have : relativeEntanglement (σ i) < relativeEntanglement (σ i) + ε :=
      ENNReal.lt_add_right (htop i) (by simpa using hε.ne')
    obtain ⟨e, ⟨τi, hsep, rfl⟩, he⟩ := sInf_lt_iff.1 this
    exact ⟨τi, hsep, he⟩
  choose τs hsep hlt using hch
  have hfin : ∀ i, relativeEntropyBits (σ i) (τs i) ≠ ⊤ := fun i => (hlt i).ne_top
  have hker : ∀ i, LinearMap.ker (τs i).mulVecLin ≤ LinearMap.ker (σ i).mulVecLin :=
    fun i => (X5PR.bits_ne_top (hfin i)).2.2
  have hτd : ∀ i, QAlgorithms.IsDensityMatrix (τs i) := fun i => X5PR.sep_dens (hsep i)
  set r : Fin d → ℝ := fun i => X5PK.relEntropy (σ i) (τs i)
  have hr0 : ∀ i, 0 ≤ r i := fun i => X5PR.relEnt_nonneg (hσd i) (hτd i) (hker i)
  -- the reference state
  set ω := (X5PR.omg τs).submatrix X5PR.pcE X5PR.pcE
  have hωd : QAlgorithms.IsDensityMatrix ω :=
    ⟨(X5PR.omg_dens hτd).1.submatrix _, by rw [X5AF.trace_sub_equiv, (X5PR.omg_dens hτd).2]⟩
  have hγd : QAlgorithms.IsDensityMatrix (partyCut (privateMatrix τ U)) :=
    ⟨hγ.1.submatrix _, by rw [X5PR.partyCut_eq, X5AF.trace_sub_equiv, hγ.2]⟩
  have hkerω : LinearMap.ker ω.mulVecLin ≤ LinearMap.ker (partyCut (privateMatrix τ U)).mulVecLin :=
    X5PR.ker_sub _ (X5PR.ker_omg U hker)
  have hval : X5PK.relEntropy (partyCut (privateMatrix τ U)) ω =
      Real.log d + (d : ℝ)⁻¹ * ∑ i, r i := by
    rw [X5PR.partyCut_eq, X5PK.relEnt_sub hγ.1.isHermitian (X5PR.omg_dens hτd).1.isHermitian,
      X5PK.relEnt_def, X5QC.mul_log _ hγ.1.isHermitian, Matrix.trace_sub, Complex.sub_re]
    show X5QC.T (privateMatrix τ U) - _ = _
    rw [X5PR.R_priv hτ U (fun i => (hτd i).1) hker]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [r, X5PK.relEnt_def, X5QC.mul_log _ (hσd i).1.isHermitian, Matrix.trace_sub,
      Complex.sub_re]
    rfl
  have hle : relativeEntanglement (partyCut (privateMatrix τ U)) ≤
      relativeEntropyBits (partyCut (privateMatrix τ U)) ω :=
    sInf_le ⟨ω, X5PR.omg_sep hsep, rfl⟩
  refine hle.trans ?_
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [X5PR.bits_eq hγd hωd hkerω, hval]
  have hbits : ∀ i, relativeEntropyBits (σ i) (τs i) = ENNReal.ofReal (r i / Real.log 2) :=
    fun i => X5PR.bits_eq (hσd i) (hτd i) (hker i)
  have e1 : (Real.log d + (d : ℝ)⁻¹ * ∑ i, r i) / Real.log 2 =
      logBits d + (d : ℝ)⁻¹ * ∑ i, r i / Real.log 2 := by
    rw [logBits, ← Finset.sum_div]; ring
  have hlog : 0 ≤ logBits (d : ℝ) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d))) hl2.le
  rw [e1, ENNReal.ofReal_add hlog (mul_nonneg (inv_nonneg.2 hd.le)
      (Finset.sum_nonneg fun i _ => div_nonneg (hr0 i) hl2.le)),
    ENNReal.ofReal_mul (inv_nonneg.2 hd.le), ENNReal.ofReal_sum_of_nonneg
      (fun i _ => div_nonneg (hr0 i) hl2.le), ENNReal.ofReal_inv_of_pos hd, ENNReal.ofReal_natCast]
  simp only [← hbits]
  rw [add_assoc]
  gcongr
  calc (d : ℝ≥0∞)⁻¹ * ∑ i, relativeEntropyBits (σ i) (τs i)
      ≤ (d : ℝ≥0∞)⁻¹ * ∑ i, (relativeEntanglement (σ i) + ε) := by
        gcongr with i; exact (hlt i).le
    _ = (d : ℝ≥0∞)⁻¹ * ∑ i, relativeEntanglement (σ i) + ε := by
        rw [Finset.sum_add_distrib, mul_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hdE (ENNReal.natCast_ne_top d), one_mul]
