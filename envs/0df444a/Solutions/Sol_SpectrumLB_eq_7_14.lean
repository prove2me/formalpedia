-- Prove2me | solution 1 for SpectrumLB.eq_7_14
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-14T05:27:39.855069+00:00
-- url     : https://prove2.me/submissions/0dd6d510-b5a7-4ec7-b15b-1e1d01b74137

/-
Direct proof of SpectrumLB.eq_7_14.
Concrete special-unitary polynomial heat, curvature, logarithmic Sobolev,
short-phase transport, Gaussian concentration, and Chernoff bounds.
All local helper theorems are proved; no Open theorem is assumed.
Lean v4.33.1; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib
import Definitions.Def_WHMultiplicativity_schattenNorm
import Definitions.Def_SpectrumLB_haarK
import Theorems.Thm_GaussianMatrix_gaussian_lipschitz_entropy_bound

set_option autoImplicit false

/- Local helper source: Solutions.Prop2PolynomialAlgebra -/
section
open scoped BigOperators Matrix

namespace BosonicLearn.Prop2
noncomputable section

section Filtration
variable {A ι : Type*} [CommRing A] [Algebra ℝ A] [Fintype ι]

/-- A finite family of monomials of fixed length. Including `1` among the generators
makes their span contain all polynomials of degree at most this length. -/
def finiteMonomial (a : ι → A) (d : ℕ) (v : Fin d → ι) : A := ∏ i, a (v i)

/-- The finite-dimensional space spanned by the length-`d` monomials. -/
def finitePolynomialSpace (a : ι → A) (d : ℕ) : Submodule ℝ A :=
  Submodule.span ℝ (Set.range (finiteMonomial a d))

instance finitePolynomialSpace_finiteDimensional (a : ι → A) (d : ℕ) :
    FiniteDimensional ℝ (finitePolynomialSpace a d) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem finiteMonomial_mem (a : ι → A) (d : ℕ) (v : Fin d → ι) :
    finiteMonomial a d v ∈ finitePolynomialSpace a d :=
  Submodule.subset_span (Set.mem_range_self v)

@[simp] theorem finiteMonomial_zero (a : ι → A) (v : Fin 0 → ι) :
    finiteMonomial a 0 v = 1 := by simp [finiteMonomial]

theorem finiteMonomial_succ (a : ι → A) (d : ℕ) (v : Fin (d+1) → ι) :
    finiteMonomial a (d+1) v = a (v 0) * finiteMonomial a d (fun j => v j.succ) := by
  simp only [finiteMonomial, Fin.prod_univ_succ]

/-- Multiplying a linear combination of generators by a degree-`d` polynomial
stays in degree `d+1`. -/
theorem generatorSpan_mul_finitePolynomialSpace (a : ι → A) (d : ℕ)
    {x y : A} (hx : x ∈ Submodule.span ℝ (Set.range a))
    (hy : y ∈ finitePolynomialSpace a d) :
    x * y ∈ finitePolynomialSpace a (d+1) := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      have h := finiteMonomial_mem a (d+1) (Fin.cons i v)
      simpa only [finiteMonomial_succ, Fin.cons_zero, Fin.cons_succ] using h
    | zero => simpa using (finitePolynomialSpace a (d+1)).zero_mem
    | add y z hy hz iy iz => simpa only [mul_add] using (finitePolynomialSpace a (d+1)).add_mem iy iz
    | smul r y hy iy => simpa only [mul_smul_comm] using (finitePolynomialSpace a (d+1)).smul_mem r iy
  | zero => simpa using (finitePolynomialSpace a (d+1)).zero_mem
  | add x z hx hz ix iz => simpa only [add_mul] using (finitePolynomialSpace a (d+1)).add_mem ix iz
  | smul r x hx ix => simpa only [smul_mul_assoc] using (finitePolynomialSpace a (d+1)).smul_mem r ix

/-- A derivation preserving the span of the linear generators preserves every
finite polynomial degree. -/
theorem finitePolynomialSpace_invariant
    (a : ι → A) (D : Derivation ℝ A A)
    (ha : ∀ i, D (a i) ∈ Submodule.span ℝ (Set.range a))
    (d : ℕ) {f : A} (hf : f ∈ finitePolynomialSpace a d) :
    D f ∈ finitePolynomialSpace a d := by
  have hmono : ∀ d (v : Fin d → ι), D (finiteMonomial a d v) ∈ finitePolynomialSpace a d := by
    intro d
    induction d with
    | zero => intro v; simp
    | succ d ih =>
      intro v
      rw [finiteMonomial_succ, D.leibniz]
      apply (finitePolynomialSpace a (d+1)).add_mem
      · exact generatorSpan_mul_finitePolynomialSpace a d
          (Submodule.subset_span (Set.mem_range_self (v 0))) (ih _)
      · simpa only [smul_eq_mul, mul_comm] using
          generatorSpan_mul_finitePolynomialSpace a d (ha (v 0))
            (finiteMonomial_mem a d (fun j => v j.succ))
  induction hf using Submodule.span_induction with
  | mem f hf => obtain ⟨v, rfl⟩ := hf; exact hmono d v
  | zero => simpa using (finitePolynomialSpace a d).zero_mem
  | add f g hf hg ihf ihg => simpa only [map_add] using (finitePolynomialSpace a d).add_mem ihf ihg
  | smul r f hf ih =>
    change D.toLinearMap (r • f) ∈ finitePolynomialSpace a d
    rw [map_smul]
    exact (finitePolynomialSpace a d).smul_mem r ih

/-- The actual finite-dimensional restriction of a degree-preserving derivation. -/
def finitePolynomialDerivative (a : ι → A) (D : Derivation ℝ A A)
    (ha : ∀ i, D (a i) ∈ Submodule.span ℝ (Set.range a)) (d : ℕ) :
    finitePolynomialSpace a d →ₗ[ℝ] finitePolynomialSpace a d :=
  D.toLinearMap.restrict (fun f hf => finitePolynomialSpace_invariant a D ha d hf)

end Filtration

theorem generatorSpan_pow_mem {A ι : Type*} [CommRing A] [Algebra ℝ A] [Fintype ι]
    (a : ι → A) {x : A} (hx : x ∈ Submodule.span ℝ (Set.range a)) (m : ℕ) :
    x ^ m ∈ finitePolynomialSpace a m := by
  induction m with
  | zero =>
    simpa using finiteMonomial_mem a 0 (fun i => Fin.elim0 i)
  | succ m ih =>
    simpa only [pow_succ, mul_comm] using generatorSpan_mul_finitePolynomialSpace a m hx ih

theorem finitePolynomialSpace_mul_mem {A ι : Type*} [CommRing A] [Algebra ℝ A] [Fintype ι]
    (a : ι → A) (d e : ℕ) {x y : A}
    (hx : x ∈ finitePolynomialSpace a d) (hy : y ∈ finitePolynomialSpace a e) :
    x * y ∈ finitePolynomialSpace a (d + e) := by
  have hmono : ∀ d (v : Fin d → ι), finiteMonomial a d v * y ∈ finitePolynomialSpace a (d + e) := by
    intro d
    induction d with
    | zero => intro v; simpa using hy
    | succ d ih =>
      intro v
      rw [finiteMonomial_succ, mul_assoc]
      have h := generatorSpan_mul_finitePolynomialSpace a (d + e)
        (Submodule.subset_span (Set.mem_range_self (v 0))) (ih (fun j => v j.succ))
      convert h using 1 <;> congr 1 <;> omega
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨v, rfl⟩ := hx; exact hmono d v
  | zero => simpa using (finitePolynomialSpace a (d + e)).zero_mem
  | add x z hx hz ix iz =>
    simpa only [add_mul] using (finitePolynomialSpace a (d + e)).add_mem ix iz
  | smul r x hx ix =>
    simpa only [smul_mul_assoc] using (finitePolynomialSpace a (d + e)).smul_mem r ix

theorem finitePolynomialSpace_pow_mem {A ι : Type*} [CommRing A] [Algebra ℝ A] [Fintype ι]
    (a : ι → A) (d : ℕ) {x : A} (hx : x ∈ finitePolynomialSpace a d) (m : ℕ) :
    x ^ m ∈ finitePolynomialSpace a (d * m) := by
  induction m with
  | zero => simpa using finiteMonomial_mem a 0 (fun i => Fin.elim0 i)
  | succ m ih =>
    simpa only [pow_succ, Nat.mul_succ] using finitePolynomialSpace_mul_mem a (d * m) d ih hx

theorem generatorSpan_finprod_mem {A ι : Type*} [CommRing A] [Algebra ℝ A] [Fintype ι]
    (a : ι → A) (d : ℕ) (x : Fin d → A)
    (hx : ∀ i, x i ∈ Submodule.span ℝ (Set.range a)) :
    (∏ i, x i) ∈ finitePolynomialSpace a d := by
  induction d with
  | zero => simpa using finiteMonomial_mem a 0 (fun i => Fin.elim0 i)
  | succ d ih =>
    rw [Fin.prod_univ_succ]
    exact generatorSpan_mul_finitePolynomialSpace a d (hx 0)
      (ih (fun j => x j.succ) (fun j => hx j.succ))


/-- The real Frobenius pairing with a fixed matrix is real-linear. -/
def realTraceAdjointMul {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℝ where
  toFun A := (Aᴴ * W).trace.re
  map_add' A B := by simp [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.trace_add]
  map_smul' r A := by simp [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.trace_smul]


end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ProductSmoothFunctions -/
section
open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator ContDiff

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 1000000

/-- Ambient algebra of finite tuples of complex matrices. -/
abbrev MatrixProduct (n K : ℕ) := Fin K → Matrix (Fin n) (Fin n) ℂ

/-- The invariant derivative in a tuple of matrix-generator directions. -/
def rightMatrixProductDerivative {n K : ℕ} (B : MatrixProduct n K)
    (f : MatrixProduct n K → ℝ) (A : MatrixProduct n K) : ℝ :=
  fderiv ℝ f A (A * B)


/-- The algebra on which the invariant matrix derivatives are actual derivations. -/
def smoothMatrixProductFunctions (n K : ℕ) :
    Subalgebra ℝ (MatrixProduct n K → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f}
  algebraMap_mem' r := by
    change ContDiff ℝ ∞ (fun _ : MatrixProduct n K => r)
    exact contDiff_const
  add_mem' := by
    intro f g hf hg
    exact (show ContDiff ℝ ∞ f from hf).add (show ContDiff ℝ ∞ g from hg)
  mul_mem' := by
    intro f g hf hg
    exact (show ContDiff ℝ ∞ f from hf).mul (show ContDiff ℝ ∞ g from hg)
  zero_mem' := by
    change ContDiff ℝ ∞ (fun _ : MatrixProduct n K => (0 : ℝ))
    exact contDiff_const
  one_mem' := by
    change ContDiff ℝ ∞ (fun _ : MatrixProduct n K => (1 : ℝ))
    exact contDiff_const

instance smoothMatrixProductFunctionsCoeFun (n K : ℕ) :
    CoeFun (smoothMatrixProductFunctions n K) (fun _ => MatrixProduct n K → ℝ) := ⟨Subtype.val⟩

theorem smoothMatrixProductFunctions_contDiff {n K : ℕ} (f : smoothMatrixProductFunctions n K) :
    ContDiff ℝ ∞ (f : MatrixProduct n K → ℝ) := f.property

theorem contDiff_rightMatrixProductDerivative {n K : ℕ}
    (B : MatrixProduct n K)
    (f : MatrixProduct n K → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (rightMatrixProductDerivative B f) := by
  exact (hf.fderiv_right (by simp)).clm_apply (contDiff_id.mul contDiff_const)

/-- The invariant differential operator on smooth ambient test functions. -/
def smoothRightMatrixProductDerivative {n K : ℕ} (B : MatrixProduct n K) :
    smoothMatrixProductFunctions n K →ₗ[ℝ] smoothMatrixProductFunctions n K where
  toFun f := ⟨rightMatrixProductDerivative B f, contDiff_rightMatrixProductDerivative B f (smoothMatrixProductFunctions_contDiff f)⟩
  map_add' f g := by
    apply Subtype.ext
    funext A
    change fderiv ℝ (fun X => f X + g X) A (A * B) =
      fderiv ℝ (f : MatrixProduct n K → ℝ) A (A * B) +
      fderiv ℝ (g : MatrixProduct n K → ℝ) A (A * B)
    rw [fderiv_fun_add ((smoothMatrixProductFunctions_contDiff f).differentiable (by simp) A)
      ((smoothMatrixProductFunctions_contDiff g).differentiable (by simp) A)]
    rfl
  map_smul' r f := by
    apply Subtype.ext
    funext A
    change fderiv ℝ (fun X => r * f X) A (A * B) =
      r * fderiv ℝ (f : MatrixProduct n K → ℝ) A (A * B)
    rw [fderiv_const_mul ((smoothMatrixProductFunctions_contDiff f).differentiable (by simp) A)]
    rfl

@[simp] theorem smoothRightMatrixProductDerivative_apply {n K : ℕ}
    (B : MatrixProduct n K) (f : smoothMatrixProductFunctions n K)
    (A : MatrixProduct n K) :
    smoothRightMatrixProductDerivative B f A = rightMatrixProductDerivative B f A := rfl

/-- Leibniz's rule on the actual smooth test-function algebra. -/
theorem smoothRightMatrixProductDerivative_mul {n K : ℕ}
    (B : MatrixProduct n K) (f g : smoothMatrixProductFunctions n K) :
    smoothRightMatrixProductDerivative B (f * g) =
      smoothRightMatrixProductDerivative B f * g + f * smoothRightMatrixProductDerivative B g := by
  apply Subtype.ext
  funext A
  change fderiv ℝ (fun X => f X * g X) A (A * B) =
    fderiv ℝ (f : MatrixProduct n K → ℝ) A (A * B) * g A +
    f A * fderiv ℝ (g : MatrixProduct n K → ℝ) A (A * B)
  rw [fderiv_fun_mul ((smoothMatrixProductFunctions_contDiff f).differentiable (by simp) A)
    ((smoothMatrixProductFunctions_contDiff g).differentiable (by simp) A)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Evaluation at an ambient matrix is an algebra homomorphism. -/
def smoothMatrixProductEvaluation {n K : ℕ} (A : MatrixProduct n K) :
    smoothMatrixProductFunctions n K →ₐ[ℝ] ℝ :=
  (Pi.evalAlgHom ℝ (fun _ : MatrixProduct n K => ℝ) A).comp
    (smoothMatrixProductFunctions n K).val


/-- Bundled derivation with its Leibniz proof, restricted to smooth functions. -/
def smoothRightMatrixProductDerivation {n K : ℕ} (B : MatrixProduct n K) :
    Derivation ℝ (smoothMatrixProductFunctions n K) (smoothMatrixProductFunctions n K) :=
  Derivation.mk' (smoothRightMatrixProductDerivative B) (fun f g => by
    simpa only [smul_eq_mul, add_comm, mul_comm] using smoothRightMatrixProductDerivative_mul B f g)

/-- Linearity of the invariant differential operator in its matrix generator. -/
def smoothRightMatrixProductDerivativeLinear (n K : ℕ) :
    MatrixProduct n K →ₗ[ℝ]
      (smoothMatrixProductFunctions n K →ₗ[ℝ] smoothMatrixProductFunctions n K) where
  toFun := smoothRightMatrixProductDerivative
  map_add' B C := by
    ext f A
    change fderiv ℝ (f : MatrixProduct n K → ℝ) A (A * (B + C)) = _
    rw [mul_add, map_add]
    rfl
  map_smul' r B := by
    ext f A
    change fderiv ℝ (f : MatrixProduct n K → ℝ) A (A * (r • B)) = _
    rw [mul_smul_comm, map_smul]
    rfl

/-- The Lie bracket of the linear vector fields `A ↦ A B` is `A ↦ A[B,C]`. -/
theorem rightMatrixProductField_lieBracket {n K : ℕ}
    (B C A : MatrixProduct n K) :
    VectorField.lieBracket ℝ (fun X : MatrixProduct n K => X * B)
      (fun X => X * C) A = A * (B * C - C * B) := by
  unfold VectorField.lieBracket
  rw [fderiv_mul_const' differentiableAt_id, fderiv_mul_const' differentiableAt_id]
  have hid : fderiv ℝ (fun X : MatrixProduct n K => X) A =
      ContinuousLinearMap.id ℝ (MatrixProduct n K) := (hasFDerivAt_id A).fderiv
  rw [hid]
  change (A * B) * C - (A * C) * B = A * (B * C - C * B)
  rw [mul_sub, mul_assoc, mul_assoc]

/-- Commutators of the concrete differential operators agree with matrix commutators. -/
theorem smoothRightMatrixProductDerivative_commutator {n K : ℕ}
    (B C : MatrixProduct n K) :
    (smoothRightMatrixProductDerivative B).comp (smoothRightMatrixProductDerivative C) -
      (smoothRightMatrixProductDerivative C).comp (smoothRightMatrixProductDerivative B) =
      smoothRightMatrixProductDerivative (B * C - C * B) := by
  ext f A
  have h := VectorField.fderiv_apply_lieBracket
    (𝕜 := ℝ) (x := A) (V := fun X : MatrixProduct n K => X * B)
    (W := fun X => X * C) (smoothMatrixProductFunctions_contDiff f).contDiffAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top)
    (differentiableAt_id.mul_const C) (differentiableAt_id.mul_const B)
  rw [rightMatrixProductField_lieBracket] at h
  exact h.symm

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2MatrixGeometry -/
section
open scoped Matrix ENNReal

namespace BosonicLearn.Prop5
noncomputable section

/-- Frobenius norm in the published Schatten convention. -/
theorem schatten_two_eq_sqrt (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 2 X = Real.sqrt (∑ i, ∑ j, ‖X j i‖ ^ 2) := by
  unfold WHMultiplicativity.schattenNorm
  rw [if_neg (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [h2]
  have hfun : (fun x : ℝ => x ^ ((2 : ℝ) / 2)) = fun x => x := by
    funext x
    rw [div_self (by norm_num), Real.rpow_one]
  rw [hfun, cfc_id' ℝ (X.conjTranspose * X)
    (by rw [← Matrix.star_eq_conjTranspose]; exact IsSelfAdjoint.star_mul_self X)]
  rw [Real.sqrt_eq_rpow]
  congr 1
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.conj_mul', ← Complex.ofReal_pow]


/-- Squared Schatten 2-norm is the trace of the Gram matrix. -/
theorem schatten_two_sq_eq_trace (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 2 A ^ 2 = (Aᴴ * A).trace.re := by
  rw [schatten_two_eq_sqrt, Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg ‖A j i‖)]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.conj_mul', ← Complex.ofReal_pow]

/-- Flattening matrix entries gives the usual Frobenius Hilbert space. -/
def frobeniusMatrixEquiv (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ ≃L[ℝ] EuclideanSpace ℂ (Fin n × Fin n) where
  toFun A := WithLp.toLp 2 (fun ij => A ij.1 ij.2)
  invFun x := fun i j => x (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := (PiLp.continuous_toLp _ _).comp (by fun_prop)
  continuous_invFun := by fun_prop

theorem norm_frobeniusMatrixEquiv (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖frobeniusMatrixEquiv n A‖ = WHMultiplicativity.schattenNorm 2 A := by
  rw [schatten_two_eq_sqrt, ← Real.sqrt_sq (norm_nonneg (frobeniusMatrixEquiv n A)),
    EuclideanSpace.norm_sq_eq]
  congr 1
  change (∑ ij : Fin n × Fin n, ‖A ij.1 ij.2‖ ^ 2) = _
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- The Frobenius norm of a unitary matrix is the square root of its dimension. -/
theorem schatten_two_unitary (n : ℕ) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 2 (U : Matrix (Fin n) (Fin n) ℂ) = Real.sqrt n := by
  have hn : 0 ≤ WHMultiplicativity.schattenNorm 2 (U : Matrix (Fin n) (Fin n) ℂ) := by
    rw [schatten_two_eq_sqrt]
    positivity
  rw [← Real.sqrt_sq hn, schatten_two_sq_eq_trace]
  have hU := Matrix.mem_unitaryGroup_iff'.mp U.property
  rw [Matrix.star_eq_conjTranspose] at hU
  rw [hU]
  simp

/-- The ambient Frobenius diameter of the unitary group is at most `2*sqrt n`. -/
theorem schatten_two_unitary_sub_le (n : ℕ)
    (U V : Matrix.unitaryGroup (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 2
      ((U : Matrix (Fin n) (Fin n) ℂ) - (V : Matrix (Fin n) (Fin n) ℂ)) ≤ 2 * Real.sqrt n := by
  rw [← norm_frobeniusMatrixEquiv, map_sub]
  calc
    _ ≤ ‖frobeniusMatrixEquiv n (U : Matrix (Fin n) (Fin n) ℂ)‖ +
        ‖frobeniusMatrixEquiv n (V : Matrix (Fin n) (Fin n) ℂ)‖ := norm_sub_le _ _
    _ = _ := by rw [norm_frobeniusMatrixEquiv, norm_frobeniusMatrixEquiv,
      schatten_two_unitary, schatten_two_unitary]; ring

section OperatorNorm
open scoped Matrix.Norms.L2Operator

theorem matrix_entry_le_operator_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖A i j‖ ≤ ‖A‖ := by
  let e := EuclideanSpace.basisFun (Fin n) ℂ
  have hi : ‖e i‖ = 1 := e.orthonormal.norm_eq_one i
  have hj : ‖e j‖ = 1 := e.orthonormal.norm_eq_one j
  have h := norm_inner_le_norm (𝕜 := ℂ) (e i) (Matrix.toEuclideanCLM (𝕜 := ℂ) A (e j))
  have he : inner ℂ (e i) (Matrix.toEuclideanCLM (𝕜 := ℂ) A (e j)) = A i j := by
    rw [EuclideanSpace.basisFun_inner]
    simp [e, EuclideanSpace.basisFun_apply, Matrix.mulVec, dotProduct]
  rw [he, hi, one_mul] at h
  have hb := (Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm (e j)
  rw [hj, mul_one] at hb
  exact h.trans hb

theorem matrix_trace_le_operator_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.trace‖ ≤ n * ‖A‖ := by
  calc
    ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin n, ‖A‖ := Finset.sum_le_sum fun i _ => matrix_entry_le_operator_norm A i i
    _ = n * ‖A‖ := by simp

end OperatorNorm

end
end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop2UnitaryHaarCore -/
section
open MeasureTheory
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section

/-- The finite-dimensional unitary group carries its Borel sigma algebra. -/
instance unitaryGroupMeasurableSpace (n : ℕ) :
    MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ) := borel _

instance unitaryGroupBorelSpace (n : ℕ) :
    BorelSpace (Matrix.unitaryGroup (Fin n) ℂ) := ⟨rfl⟩

/-- Finite-dimensional unitary groups are compact. -/
instance unitaryGroupCompactSpace (n : ℕ) :
    CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) := by
  apply isCompact_iff_compactSpace.mp
  apply Metric.isCompact_of_isClosed_isBounded isClosed_unitary
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1, ?_⟩
  intro U hU
  rcases subsingleton_or_nontrivial (Matrix (Fin n) (Fin n) ℂ) with h | h
  · simp only [Subsingleton.elim U 0, norm_zero, zero_le_one]
  · exact (CStarRing.norm_of_mem_unitary hU).le

/-- Probability Haar measure on the unitary group. -/
def unitaryHaar (n : ℕ) : Measure (Matrix.unitaryGroup (Fin n) ℂ) :=
  Measure.haarMeasure ⊤

deriving instance Measure.IsHaarMeasure for unitaryHaar

instance unitaryHaar_probability (n : ℕ) : IsProbabilityMeasure (unitaryHaar n) :=
  ⟨Measure.haarMeasure_self⟩

/-- Continuous functions on the unitary group are Haar integrable. -/
theorem continuous_integrable_unitaryHaar {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (f : Matrix.unitaryGroup (Fin n) ℂ → E) (hf : Continuous f) :
    Integrable f (unitaryHaar n) :=
  hf.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset isClosed_closure (by simp))

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2PhaseGeometry -/
section
open MeasureTheory
open scoped Matrix ENNReal

namespace BosonicLearn.Prop2
noncomputable section

theorem norm_phase_sub_phase_le (θ φ : ℝ) :
    ‖Complex.exp (Complex.I * θ) - Complex.exp (Complex.I * φ)‖ ≤ |θ - φ| := by
  have heq : Complex.exp (Complex.I * θ) - Complex.exp (Complex.I * φ) =
      (Complex.exp (Complex.I * (θ - φ)) - 1) * Complex.exp (Complex.I * φ) := by
    rw [sub_mul, ← Complex.exp_add, one_mul]
    congr 2
    push_cast
    ring
  rw [heq, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  simpa only [Real.norm_eq_abs, Complex.ofReal_sub] using
    Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ - φ)

/-- Multiplication by a scalar phase, as an actual unitary-group map. -/
def phaseMultiply {n : ℕ} (θ : ℝ) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨Complex.exp (Complex.I * θ) • (U : Matrix (Fin n) (Fin n) ℂ), by
    apply Matrix.mem_unitaryGroup_iff.mpr
    rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Unitary.mul_star_self_of_mem U.property]
    have hc : Complex.exp (Complex.I * θ) * star (Complex.exp (Complex.I * θ)) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.norm_exp_I_mul_ofReal]
      norm_num
    rw [hc, one_smul]⟩

@[simp] theorem phaseMultiply_coe {n : ℕ} (θ : ℝ) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (phaseMultiply θ U : Matrix (Fin n) (Fin n) ℂ) =
      Complex.exp (Complex.I * θ) • (U : Matrix (Fin n) (Fin n) ℂ) := rfl

theorem continuous_phaseMultiply (n : ℕ) :
    Continuous (fun p : ℝ × Matrix.unitaryGroup (Fin n) ℂ => phaseMultiply p.1 p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : ℝ × Matrix.unitaryGroup (Fin n) ℂ =>
    Complex.exp (Complex.I * p.1) • (p.2 : Matrix (Fin n) (Fin n) ℂ))
  fun_prop

theorem schatten_two_complex_smul {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 2 (c • A) = ‖c‖ * WHMultiplicativity.schattenNorm 2 A := by
  rw [← Prop5.norm_frobeniusMatrixEquiv, ← Prop5.norm_frobeniusMatrixEquiv]
  change ‖c • Prop5.frobeniusMatrixEquiv n A‖ = ‖c‖ * ‖Prop5.frobeniusMatrixEquiv n A‖
  exact norm_smul c _

/-- The special-unitary factor is unaffected metrically by fixing the scalar phase. -/
theorem phaseMultiply_schatten_distance {n : ℕ} (θ : ℝ)
    (U V : Matrix.unitaryGroup (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 2
      ((phaseMultiply θ U : Matrix (Fin n) (Fin n) ℂ) -
        (phaseMultiply θ V : Matrix (Fin n) (Fin n) ℂ)) =
      WHMultiplicativity.schattenNorm 2
        ((U : Matrix (Fin n) (Fin n) ℂ) - (V : Matrix (Fin n) (Fin n) ℂ)) := by
  rw [phaseMultiply_coe, phaseMultiply_coe, ← smul_sub, schatten_two_complex_smul,
    Complex.norm_exp_I_mul_ofReal, one_mul]

/-- The phase coordinate has Frobenius Lipschitz constant `sqrt n`. -/
theorem phaseMultiply_schatten_phase_le {n : ℕ} (θ φ : ℝ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 2
      ((phaseMultiply θ U : Matrix (Fin n) (Fin n) ℂ) -
        (phaseMultiply φ U : Matrix (Fin n) (Fin n) ℂ)) ≤
      Real.sqrt n * |θ - φ| := by
  rw [phaseMultiply_coe, phaseMultiply_coe, ← sub_smul, schatten_two_complex_smul,
    Prop5.schatten_two_unitary]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_right (norm_phase_sub_phase_le θ φ) (Real.sqrt_nonneg n)

/-- The Euclidean product of ambient Frobenius distances. -/
def unitaryProductFrobeniusDist {n K : ℕ}
    (U V : Fin K → Matrix.unitaryGroup (Fin n) ℂ) : ℝ :=
  Real.sqrt (∑ i, (WHMultiplicativity.schattenNorm 2
    ((U i : Matrix (Fin n) (Fin n) ℂ) - (V i : Matrix (Fin n) (Fin n) ℂ))) ^ 2)

def phaseCubeMultiply {n K : ℕ} (θ : Fin K → ℝ)
    (U : Fin K → Matrix.unitaryGroup (Fin n) ℂ) : Fin K → Matrix.unitaryGroup (Fin n) ℂ :=
  fun i => phaseMultiply (θ i) (U i)

theorem continuous_phaseCubeMultiply (n K : ℕ) :
    Continuous (fun p : (Fin K → ℝ) × (Fin K → Matrix.unitaryGroup (Fin n) ℂ) =>
      phaseCubeMultiply p.1 p.2) := by
  apply continuous_pi
  intro i
  have hp : Continuous (fun p : (Fin K → ℝ) × (Fin K → Matrix.unitaryGroup (Fin n) ℂ) =>
      (p.1 i, p.2 i)) := by fun_prop
  exact (continuous_phaseMultiply n).comp hp

theorem phaseCubeMultiply_distance {n K : ℕ} (θ : Fin K → ℝ)
    (U V : Fin K → Matrix.unitaryGroup (Fin n) ℂ) :
    unitaryProductFrobeniusDist (phaseCubeMultiply θ U) (phaseCubeMultiply θ V) =
      unitaryProductFrobeniusDist U V := by
  simp only [unitaryProductFrobeniusDist, phaseCubeMultiply, phaseMultiply_schatten_distance]

/-- The entire phase cube, in Euclidean distance, has Lipschitz constant `sqrt n`,
independent of the number of unitary factors. -/
theorem phaseCubeMultiply_phase_distance_le {n K : ℕ} (θ φ : Fin K → ℝ)
    (U : Fin K → Matrix.unitaryGroup (Fin n) ℂ) :
    unitaryProductFrobeniusDist (phaseCubeMultiply θ U) (phaseCubeMultiply φ U) ≤
      Real.sqrt n * Real.sqrt (∑ i, (θ i - φ i) ^ 2) := by
  have hsq (i : Fin K) :
      (WHMultiplicativity.schattenNorm 2
        ((phaseMultiply (θ i) (U i) : Matrix (Fin n) (Fin n) ℂ) -
          (phaseMultiply (φ i) (U i) : Matrix (Fin n) (Fin n) ℂ))) ^ 2 ≤
        n * (θ i - φ i) ^ 2 := by
    have h := phaseMultiply_schatten_phase_le (θ i) (φ i) (U i)
    have hnonneg : 0 ≤ WHMultiplicativity.schattenNorm 2
        ((phaseMultiply (θ i) (U i) : Matrix (Fin n) (Fin n) ℂ) -
          (phaseMultiply (φ i) (U i) : Matrix (Fin n) (Fin n) ℂ)) := by
      rw [Prop5.schatten_two_eq_sqrt]
      positivity
    have hp := pow_le_pow_left₀ hnonneg h 2
    simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), sq_abs] using hp
  calc
    _ ≤ Real.sqrt (∑ i, (n : ℝ) * (θ i - φ i) ^ 2) := by
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum (fun i _ => hsq i)
    _ = _ := by rw [← Finset.mul_sum, Real.sqrt_mul (Nat.cast_nonneg n)]

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2SpecialUnitaryHaar -/
section
open MeasureTheory Set
open scoped Matrix ENNReal Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 2000000

instance specialUnitaryGroupMeasurableSpace (n : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin n) ℂ) := borel _
instance specialUnitaryGroupBorelSpace (n : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin n) ℂ) := ⟨rfl⟩

instance specialUnitaryGroupContinuousInv (n : ℕ) :
    ContinuousInv (Matrix.specialUnitaryGroup (Fin n) ℂ) := by
  constructor
  exact continuous_induced_rng.mpr continuous_subtype_val.star

instance specialUnitaryGroupCompactSpace (n : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin n) ℂ) := by
  apply isCompact_iff_compactSpace.mp
  apply Metric.isCompact_of_isClosed_isBounded
  · change IsClosed ({A : Matrix (Fin n) (Fin n) ℂ | A ∈ Matrix.unitaryGroup (Fin n) ℂ} ∩
      {A | A.det = 1})
    exact isClosed_unitary.inter (isClosed_eq (by fun_prop) continuous_const)
  · apply isBounded_iff_forall_norm_le.mpr
    refine ⟨1, ?_⟩
    intro U hU
    rcases subsingleton_or_nontrivial (Matrix (Fin n) (Fin n) ℂ) with h | h
    · simp only [Subsingleton.elim U 0, norm_zero, zero_le_one]
    · exact (CStarRing.norm_of_mem_unitary hU.1).le

instance specialUnitaryGroupTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin n) ℂ) where
  continuous_mul := continuous_induced_rng.mpr
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd))
  continuous_inv := continuous_induced_rng.mpr continuous_subtype_val.star

/-- The normalized Haar law on the special-unitary group. -/
def specialUnitaryHaar (n : ℕ) : Measure (Matrix.specialUnitaryGroup (Fin n) ℂ) :=
  Measure.haarMeasure ⊤
deriving instance Measure.IsHaarMeasure for specialUnitaryHaar
instance specialUnitaryHaar_probability (n : ℕ) :
    IsProbabilityMeasure (specialUnitaryHaar n) := ⟨Measure.haarMeasure_self⟩

/-- Inclusion of determinant-one unitaries into all unitaries. -/
def specialUnitaryInclusion (n : ℕ) :
    Matrix.specialUnitaryGroup (Fin n) ℂ →* Matrix.unitaryGroup (Fin n) ℂ :=
  Submonoid.inclusion Matrix.specialUnitaryGroup_le_unitaryGroup

theorem continuous_specialUnitaryInclusion (n : ℕ) :
    Continuous (specialUnitaryInclusion n) := continuous_subtype_val.subtype_mk _

instance circleMeasurableSpace : MeasurableSpace Circle := borel _
instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

def circleHaar : Measure Circle := Measure.haarMeasure ⊤
deriving instance Measure.IsHaarMeasure for circleHaar
instance circleHaar_probability : IsProbabilityMeasure circleHaar := ⟨Measure.haarMeasure_self⟩

/-- Multiplication of a special unitary by a scalar of modulus one. -/
def circleSpecialUnitaryProduct (n : ℕ) :
    Circle × Matrix.specialUnitaryGroup (Fin n) ℂ →* Matrix.unitaryGroup (Fin n) ℂ where
  toFun p := ⟨(p.1 : ℂ) • (p.2 : Matrix (Fin n) (Fin n) ℂ), by
    apply Matrix.mem_unitaryGroup_iff.mpr
    rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Unitary.mul_star_self_of_mem p.2.property.1]
    have hc : (p.1 : ℂ) * star (p.1 : ℂ) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
      norm_num
    rw [hc, one_smul]⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' p q := by
    apply Subtype.ext
    change ((p.1 * q.1 : Circle) : ℂ) •
      ((p.2 : Matrix (Fin n) (Fin n) ℂ) * (q.2 : Matrix (Fin n) (Fin n) ℂ)) =
      ((p.1 : ℂ) • (p.2 : Matrix (Fin n) (Fin n) ℂ)) *
      ((q.1 : ℂ) • (q.2 : Matrix (Fin n) (Fin n) ℂ))
    rw [Circle.coe_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem continuous_circleSpecialUnitaryProduct (n : ℕ) :
    Continuous (circleSpecialUnitaryProduct n) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)

theorem circleSpecialUnitaryProduct_surjective {n : ℕ} (hn : 1 ≤ n) :
    Function.Surjective (circleSpecialUnitaryProduct n) := by
  intro U
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq
    (Matrix.det (U : Matrix (Fin n) (Fin n) ℂ)) (by omega : 0 < n)
  have hzNorm : ‖z‖ = 1 := by
    have hp : ‖z‖ ^ n = (1 : ℝ) ^ n := by
      rw [← norm_pow, hz, CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary U.property)]
      simp
    exact (pow_left_inj₀ (norm_nonneg z) zero_le_one (by omega : n ≠ 0)).mp hp
  let c : Circle := ⟨z, by simpa [Submonoid.unitSphere] using hzNorm⟩
  let V : Matrix (Fin n) (Fin n) ℂ := z⁻¹ • (U : Matrix (Fin n) (Fin n) ℂ)
  have hz0 : z ≠ 0 := by intro h; simp [h] at hzNorm
  have hVu : V ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    dsimp [V]
    rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Unitary.mul_star_self_of_mem U.property]
    have hc : z⁻¹ * star z⁻¹ = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_inv, hzNorm]
      norm_num
    rw [hc, one_smul]
  have hVd : V.det = 1 := by
    dsimp [V]
    rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hz]
    exact inv_mul_cancel₀ (Matrix.UnitaryGroup.det_isUnit U).ne_zero
  refine ⟨(c, ⟨V, hVu, hVd⟩), ?_⟩
  apply Subtype.ext
  change z • (z⁻¹ • (U : Matrix (Fin n) (Fin n) ℂ)) = _
  rw [smul_smul, mul_inv_cancel₀ hz0, one_smul]

theorem circleSpecialUnitaryProduct_measurePreserving {n : ℕ} (hn : 1 ≤ n) :
    MeasurePreserving (circleSpecialUnitaryProduct n)
      (circleHaar.prod (specialUnitaryHaar n)) (unitaryHaar n) :=
  MonoidHom.measurePreserving (continuous_circleSpecialUnitaryProduct n)
    (circleSpecialUnitaryProduct_surjective hn) (by simp)


local instance twoPiPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private theorem addCircleToCircle_measurePreserving :
    MeasurePreserving (@AddCircle.toCircle (2 * Real.pi)) AddCircle.haarAddCircle circleHaar := by
  let μ : Measure Circle := AddCircle.haarAddCircle.map (@AddCircle.toCircle (2 * Real.pi))
  have hm : Measurable (@AddCircle.toCircle (2 * Real.pi)) := AddCircle.continuous_toCircle.measurable
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hm.aemeasurable
  have : Measure.IsMulLeftInvariant μ := by
    constructor
    intro z
    obtain ⟨a, ha⟩ := (AddCircle.homeomorphCircle (by positivity : 2 * Real.pi ≠ 0)).surjective z
    rw [AddCircle.homeomorphCircle_apply] at ha
    change (AddCircle.haarAddCircle.map AddCircle.toCircle).map (z * ·) = _
    have hzm : Measurable (fun x : Circle => z * x) := by fun_prop
    rw [Measure.map_map hzm hm]
    have heq : (fun x : AddCircle (2 * Real.pi) => z * x.toCircle) =
        fun x => (a + x).toCircle := by
      funext x
      rw [AddCircle.toCircle_add, ha]
    have ham : Measurable (fun x : AddCircle (2 * Real.pi) => a + x) := by fun_prop
    change AddCircle.haarAddCircle.map (fun x : AddCircle (2 * Real.pi) => z * x.toCircle) = μ
    rw [heq]
    change AddCircle.haarAddCircle.map (AddCircle.toCircle ∘ (fun x => a + x)) = μ
    rw [← Measure.map_map hm ham, Measure.IsAddLeftInvariant.map_add_left_eq_self]
  have hscale := Measure.isMulLeftInvariant_eq_smul μ circleHaar
  have hmass := congrArg (fun ρ : Measure Circle => ρ univ) hscale
  have hfactor : Measure.haarScalarFactor μ circleHaar = 1 := by simpa using hmass.symm
  refine ⟨hm, ?_⟩
  change μ = circleHaar
  simpa [hfactor] using hscale

/-- Haar integration on the scalar unit circle is normalized integration of the phase. -/
theorem integral_circleHaar (f : Circle → ℝ) (hf : Continuous f) :
    ∫ z, f z ∂circleHaar = (2 * Real.pi)⁻¹ * ∫ θ in 0..2 * Real.pi, f (Circle.exp θ) := by
  rw [← addCircleToCircle_measurePreserving.map_eq,
    integral_map addCircleToCircle_measurePreserving.measurable.aemeasurable hf.aestronglyMeasurable]
  change (∫ z : AddCircle (2 * Real.pi), f (AddCircle.toCircle z) ∂AddCircle.haarAddCircle) = _
  rw [AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (2 * Real.pi) 0 (fun z => f (AddCircle.toCircle z))]
  simp only [zero_add, smul_eq_mul, AddCircle.toCircle_apply_mk,
    div_self (by positivity : 2 * Real.pi ≠ 0), one_mul]

/-- A central scalar root of unity is special unitary. -/
def specialUnitaryCentralRoot {n : ℕ} (hn : 1 ≤ n) :
    Matrix.specialUnitaryGroup (Fin n) ℂ := by
  let c := Circle.exp (2 * Real.pi / n)
  let U := circleSpecialUnitaryProduct n (c, 1)
  refine ⟨(U : Matrix (Fin n) (Fin n) ℂ), U.property, ?_⟩
  change Matrix.det ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) = 1
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have he : c ^ n = 1 := by
    dsimp [c]
    rw [← Circle.exp_natCast_mul, mul_div_cancel₀ (2 * Real.pi) hn0, Circle.exp_two_pi]
  exact congrArg (fun z : Circle => (z : ℂ)) he

/-- Integrating over special unitaries removes the central scalar root of unity. -/
theorem specialUnitary_phase_average_periodic {n : ℕ} (hn : 1 ≤ n)
    (f : Matrix.unitaryGroup (Fin n) ℂ → ℝ) :
    Function.Periodic
      (fun θ => ∫ V, f (circleSpecialUnitaryProduct n (Circle.exp θ, V)) ∂specialUnitaryHaar n)
      (2 * Real.pi / n) := by
  intro θ
  have hpoint : ∀ V : Matrix.specialUnitaryGroup (Fin n) ℂ,
      circleSpecialUnitaryProduct n (Circle.exp (θ + 2 * Real.pi / n), V) =
      circleSpecialUnitaryProduct n (Circle.exp θ, specialUnitaryCentralRoot hn * V) := by
    intro V
    apply Subtype.ext
    change ((Circle.exp (θ + 2 * Real.pi / n) : Circle) : ℂ) •
      (V : Matrix (Fin n) (Fin n) ℂ) =
      (Circle.exp θ : ℂ) •
        (((Circle.exp (2 * Real.pi / n) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) *
          (V : Matrix (Fin n) (Fin n) ℂ))
    rw [Circle.exp_add, Circle.coe_mul, Matrix.smul_mul, one_mul, smul_smul]
  simp_rw [hpoint]
  exact integral_mul_left_eq_self
    (fun V => f (circleSpecialUnitaryProduct n (Circle.exp θ, V))) (specialUnitaryCentralRoot hn)

theorem continuous_specialUnitary_phase_average {n : ℕ}
    (f : Matrix.unitaryGroup (Fin n) ℂ → ℝ) (hf : Continuous f) :
    Continuous (fun θ =>
      ∫ V, f (circleSpecialUnitaryProduct n (Circle.exp θ, V)) ∂specialUnitaryHaar n) := by
  have hc : Continuous (fun p : ℝ × Matrix.specialUnitaryGroup (Fin n) ℂ =>
      f (circleSpecialUnitaryProduct n (Circle.exp p.1, p.2))) :=
    hf.comp ((continuous_circleSpecialUnitaryProduct n).comp
      ((Circle.exp.continuous.comp continuous_fst).prodMk continuous_snd))
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous (μ := specialUnitaryHaar n) hc isCompact_univ)


private theorem integrable_continuous_unitary_comp_suHaar {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Matrix.unitaryGroup (Fin n) ℂ → ℝ) (hf : Continuous f)
    (g : Ω → Matrix.unitaryGroup (Fin n) ℂ) (hg : Measurable g) :
    Integrable (fun x => f (g x)) μ := by
  have hfi : Integrable f (μ.map g) :=
    hf.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset isClosed_closure (by simp))
  exact hfi.comp_measurable hg

/-- Continuous Haar integrals can be computed using a phase interval of length `2π/n`
and an independent special-unitary Haar matrix. -/
theorem integral_unitaryHaar_short_phase {n : ℕ} (hn : 1 ≤ n)
    (f : Matrix.unitaryGroup (Fin n) ℂ → ℝ) (hf : Continuous f) :
    ∫ U, f U ∂unitaryHaar n =
      (2 * Real.pi / n)⁻¹ * ∫ θ in 0..2 * Real.pi / n,
        ∫ V, f (circleSpecialUnitaryProduct n (Circle.exp θ, V)) ∂specialUnitaryHaar n := by
  let g : ℝ → ℝ := fun θ =>
    ∫ V, f (circleSpecialUnitaryProduct n (Circle.exp θ, V)) ∂specialUnitaryHaar n
  have hg : Continuous g := continuous_specialUnitary_phase_average f hf
  have hp : Function.Periodic g (2 * Real.pi / n) := specialUnitary_phase_average_periodic hn f
  have hperiod := hp.intervalIntegral_add_zsmul_eq (n : ℤ) 0 hg.intervalIntegrable
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hperiod' : (∫ θ in 0..2 * Real.pi, g θ) = (n : ℝ) * ∫ θ in 0..2 * Real.pi / n, g θ := by
    convert hperiod using 1 <;> simp only [zero_add, zsmul_eq_mul, Int.cast_natCast]
    rw [mul_div_cancel₀ _ hn0]
  have hc : Continuous (fun z : Circle =>
      ∫ V, f (circleSpecialUnitaryProduct n (z, V)) ∂specialUnitaryHaar n) := by
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous (μ := specialUnitaryHaar n)
        (f := fun z V => f (circleSpecialUnitaryProduct n (z, V)))
        (hf.comp (continuous_circleSpecialUnitaryProduct n)) isCompact_univ)
  rw [← (circleSpecialUnitaryProduct_measurePreserving hn).map_eq,
    integral_map (continuous_circleSpecialUnitaryProduct n).measurable.aemeasurable hf.aestronglyMeasurable,
    integral_prod _ (integrable_continuous_unitary_comp_suHaar _ f hf _
      (continuous_circleSpecialUnitaryProduct n).measurable), integral_circleHaar _ hc]
  change (2 * Real.pi)⁻¹ * (∫ θ in 0..2 * Real.pi, g θ) = _
  rw [hperiod']
  simp only [inv_div]
  ring

/-- The uniform phase law on the half-open interval `[0,2π/n)`. -/
def shortPhaseLaw (n : ℕ) : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi / n))⁻¹ • volume.restrict (Ico 0 (2 * Real.pi / n))

theorem shortPhaseLaw_probability {n : ℕ} (hn : 1 ≤ n) :
    IsProbabilityMeasure (shortPhaseLaw n) := by
  constructor
  have hT : 0 < 2 * Real.pi / n := by positivity
  simp only [shortPhaseLaw, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Ico, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simpa using hT : ENNReal.ofReal (2 * Real.pi / n) ≠ 0) ENNReal.ofReal_ne_top

theorem shortPhaseLaw_ae_mem_Icc {n : ℕ} :
    ∀ᵐ θ ∂shortPhaseLaw n, θ ∈ Icc 0 (2 * Real.pi / n) := by
  apply Measure.ae_smul_measure _
  filter_upwards [ae_restrict_mem measurableSet_Ico] with θ hθ
  exact Ico_subset_Icc_self hθ

theorem integral_shortPhaseLaw {n : ℕ} (hn : 1 ≤ n) (g : ℝ → ℝ) :
    ∫ θ, g θ ∂shortPhaseLaw n =
      (2 * Real.pi / n)⁻¹ * ∫ θ in 0..2 * Real.pi / n, g θ := by
  have hT : 0 ≤ 2 * Real.pi / n := by positivity
  rw [shortPhaseLaw, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal hT,
    smul_eq_mul, restrict_Ico_eq_restrict_Ioc,
    intervalIntegral.integral_of_le hT]

/-- An independent short uniform phase and special-unitary Haar matrix produce Haar `U(n)`. -/
theorem shortPhase_specialUnitary_map {n : ℕ} (hn : 1 ≤ n) :
    ((shortPhaseLaw n).prod (specialUnitaryHaar n)).map
      (fun p => circleSpecialUnitaryProduct n (Circle.exp p.1, p.2)) = unitaryHaar n := by
  have : IsProbabilityMeasure (shortPhaseLaw n) := shortPhaseLaw_probability hn
  have hc : Continuous (fun p : ℝ × Matrix.specialUnitaryGroup (Fin n) ℂ =>
      circleSpecialUnitaryProduct n (Circle.exp p.1, p.2)) :=
    (continuous_circleSpecialUnitaryProduct n).comp
      ((Circle.exp.continuous.comp continuous_fst).prodMk continuous_snd)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hf : Continuous (fun U => f U) := f.continuous
  rw [integral_map hc.measurable.aemeasurable hf.aestronglyMeasurable,
    integral_prod _ (integrable_continuous_unitary_comp_suHaar _ f f.continuous _ hc.measurable),
    integral_shortPhaseLaw hn]
  exact (integral_unitaryHaar_short_phase hn f f.continuous).symm


/-- Special-unitary Haar measure viewed as a probability law on `U(n)`. -/
def specialUnitaryHaarOnUnitary (n : ℕ) : Measure (Matrix.unitaryGroup (Fin n) ℂ) :=
  (specialUnitaryHaar n).map (specialUnitaryInclusion n)

instance specialUnitaryHaarOnUnitary_probability (n : ℕ) :
    IsProbabilityMeasure (specialUnitaryHaarOnUnitary n) :=
  Measure.isProbabilityMeasure_map (continuous_specialUnitaryInclusion n).measurable.aemeasurable

/-- The scalar/SU factorization in the ambient unitary group, ready for analytic tensorization. -/
theorem shortPhase_unitary_map {n : ℕ} (hn : 1 ≤ n) :
    ((shortPhaseLaw n).prod (specialUnitaryHaarOnUnitary n)).map
      (fun p => phaseMultiply p.1 p.2) = unitaryHaar n := by
  have : IsProbabilityMeasure (shortPhaseLaw n) := shortPhaseLaw_probability hn
  have hprod : (shortPhaseLaw n).prod (specialUnitaryHaarOnUnitary n) =
      ((shortPhaseLaw n).prod (specialUnitaryHaar n)).map
        (Prod.map id (specialUnitaryInclusion n)) := by
    simpa only [Measure.map_id, specialUnitaryHaarOnUnitary] using
      (Measure.map_prod_map (shortPhaseLaw n) (specialUnitaryHaar n) measurable_id
        (continuous_specialUnitaryInclusion n).measurable)
  rw [hprod, Measure.map_map (continuous_phaseMultiply n).measurable
    (measurable_id.prodMap (continuous_specialUnitaryInclusion n).measurable)]
  convert shortPhase_specialUnitary_map hn using 1
  congr 1
  funext p
  apply Subtype.ext
  change Complex.exp (Complex.I * (p.1 : ℂ)) • (p.2 : Matrix (Fin n) (Fin n) ℂ) =
    Complex.exp ((p.1 : ℂ) * Complex.I) • (p.2 : Matrix (Fin n) (Fin n) ℂ)
  rw [mul_comm Complex.I]

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2RangeDescended -/
section
namespace BosonicLearn.Prop2
noncomputable section

/-- An invariant linear operator descends to the image of a linear restriction map. -/
def rangeDescendedOperator {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (R : E →ₗ[ℝ] F) (D : E →ₗ[ℝ] E)
    (hker : ∀ f, R f = 0 → R (D f) = 0) : R.range →ₗ[ℝ] R.range :=
  R.quotKerEquivRange.toLinearMap.comp
    ((R.ker.mapQ R.ker D (fun f hf => LinearMap.mem_ker.mpr (hker f (LinearMap.mem_ker.mp hf)))).comp R.quotKerEquivRange.symm.toLinearMap)

@[simp] theorem rangeDescendedOperator_apply_image {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (R : E →ₗ[ℝ] F) (D : E →ₗ[ℝ] E)
    (hker : ∀ f, R f = 0 → R (D f) = 0) (f : E) :
    (rangeDescendedOperator R D hker (R.rangeRestrict f) : F) = R (D f) := by
  dsimp only [rangeDescendedOperator, LinearMap.comp_apply, LinearEquiv.coe_coe]
  change (R.quotKerEquivRange (R.ker.mapQ R.ker D _
    (R.quotKerEquivRange.symm ⟨R f, LinearMap.mem_range_self R f⟩)) : F) = _
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  change (R.quotKerEquivRange (Submodule.Quotient.mk (D f)) : F) = _
  exact R.quotKerEquivRange_apply_mk (D f)


end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2Casimir -/
section
open scoped Matrix BigOperators ComplexConjugate

namespace BosonicLearn.Prop2

noncomputable section

/-- The square of the Hilbert--Schmidt norm, written without choosing a matrix
norm instance. -/
def matrixFrobeniusSq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (A i j)

theorem matrixFrobeniusSq_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) : 0 ≤ matrixFrobeniusSq A := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem matrixFrobeniusSq_eq_sum_norm_sq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) : matrixFrobeniusSq A = ∑ i, ∑ j, ‖A i j‖^2 := by
  simp [matrixFrobeniusSq, Complex.normSq_eq_norm_sq]

/-- A matrix-unit commutator has one nonzero row and one nonzero column; their
intersection contributes the trace cross term. -/
theorem matrixFrobeniusSq_single_commutator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i j : ι) :
    matrixFrobeniusSq (Matrix.single i j 1 * A - A * Matrix.single i j 1) =
      (∑ b, Complex.normSq (A j b)) + (∑ a, Complex.normSq (A a i)) -
        2 * (A j j * conj (A i i)).re := by
  have hentry (a b : ι) :
      Complex.normSq (((Matrix.single i j 1 * A - A * Matrix.single i j 1) : Matrix ι ι ℂ) a b) =
        (if a = i then Complex.normSq (A j b) else 0) +
        (if b = j then Complex.normSq (A a i) else 0) -
        (if a = i ∧ b = j then 2 * (A j j * conj (A i i)).re else 0) := by
    by_cases ha : a = i <;> by_cases hb : b = j
    · subst a; subst b
      simp [Complex.normSq_sub]
    · subst a
      simp [Matrix.sub_apply, Matrix.mul_single_apply_of_ne _ _ _ _ _ hb, hb]
    · subst b
      simp [Matrix.sub_apply, Matrix.single_mul_apply_of_ne _ _ _ _ _ ha, ha]
    · simp [Matrix.sub_apply, Matrix.single_mul_apply_of_ne _ _ _ _ _ ha,
        Matrix.mul_single_apply_of_ne _ _ _ _ _ hb, ha, hb]
  simp only [matrixFrobeniusSq, hentry, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp [ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.sum_ite_eq]

/-- The adjoint Casimir identity for all complex matrices. Its trace-zero
specialization is the algebraic core of the Ricci bound for the special unitary
group with the Hilbert--Schmidt metric. -/
theorem matrix_unit_casimir {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    (∑ i, ∑ j, matrixFrobeniusSq
      (Matrix.single i j 1 * A - A * Matrix.single i j 1)) =
      2 * Fintype.card ι * matrixFrobeniusSq A - 2 * Complex.normSq A.trace := by
  simp_rw [matrixFrobeniusSq_single_commutator, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  have hcross : (∑ i : ι, ∑ j : ι, 2 * (A j j * conj (A i i)).re) =
      2 * Complex.normSq A.trace := by
    simp_rw [← Finset.mul_sum]
    congr 1
    have hn : Complex.normSq A.trace = (conj A.trace * A.trace).re := by
      exact congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := A.trace))
    rw [hn]
    simp only [Matrix.trace, Matrix.diag_apply, map_sum, Finset.mul_sum, Finset.sum_mul,
      Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [hcross]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have hswap : (∑ i, ∑ a, Complex.normSq (A a i)) = matrixFrobeniusSq A := by
    exact Finset.sum_comm
  rw [hswap]
  unfold matrixFrobeniusSq
  ring

theorem matrix_unit_casimir_traceless {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.trace = 0) :
    (∑ i, ∑ j, matrixFrobeniusSq
      (Matrix.single i j 1 * A - A * Matrix.single i j 1)) =
      2 * Fintype.card ι * matrixFrobeniusSq A := by
  rw [matrix_unit_casimir, hA]
  simp


/-- Complex scalar multiplication rescales the squared Hilbert--Schmidt norm by
its squared complex modulus. -/
theorem matrixFrobeniusSq_smul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ℂ) (A : Matrix ι κ ℂ) :
    matrixFrobeniusSq (c • A) = Complex.normSq c * matrixFrobeniusSq A := by
  simp [matrixFrobeniusSq, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]

theorem matrixFrobeniusSq_parallelogram {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A B : Matrix ι κ ℂ) :
    matrixFrobeniusSq (A + B) + matrixFrobeniusSq (A - B) =
      2 * (matrixFrobeniusSq A + matrixFrobeniusSq B) := by
  simp only [matrixFrobeniusSq, Matrix.add_apply, Matrix.sub_apply, Complex.normSq_add,
    Complex.normSq_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- Two skew-Hermitian directions for each ordered pair. Their repetitions and
scalings give a Parseval frame for the real unitary Lie algebra. -/
def skewRealGenerator {ι : Type*} [DecidableEq ι] (i j : ι) : Matrix ι ι ℂ :=
  (1/2 : ℂ) • (Matrix.single i j 1 - Matrix.single j i 1)

def skewImagGenerator {ι : Type*} [DecidableEq ι] (i j : ι) : Matrix ι ι ℂ :=
  (Complex.I/2) • (Matrix.single i j 1 + Matrix.single j i 1)

theorem skewRealGenerator_conjTranspose {ι : Type*} [DecidableEq ι] (i j : ι) :
    (skewRealGenerator i j)ᴴ = -skewRealGenerator i j := by
  simp [skewRealGenerator, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_single, ← smul_neg, neg_sub]

theorem skewImagGenerator_conjTranspose {ι : Type*} [DecidableEq ι] (i j : ι) :
    (skewImagGenerator i j)ᴴ = -skewImagGenerator i j := by
  simp [skewImagGenerator, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_single, add_comm, ← Matrix.single_neg, neg_div]

/-- Pairing the real and imaginary generators eliminates their cross terms. -/
theorem skew_generator_pair_commutator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i j : ι) :
    matrixFrobeniusSq (skewRealGenerator i j * A - A * skewRealGenerator i j) +
      matrixFrobeniusSq (skewImagGenerator i j * A - A * skewImagGenerator i j) =
      (matrixFrobeniusSq (Matrix.single i j 1 * A - A * Matrix.single i j 1) +
        matrixFrobeniusSq (Matrix.single j i 1 * A - A * Matrix.single j i 1)) / 2 := by
  let B := Matrix.single i j 1 * A - A * Matrix.single i j 1
  let C := Matrix.single j i 1 * A - A * Matrix.single j i 1
  have hr : skewRealGenerator i j * A - A * skewRealGenerator i j =
      (1/2 : ℂ) • (B-C) := by
    dsimp [skewRealGenerator, B, C]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub, sub_mul, mul_sub]
    abel
  have hi : skewImagGenerator i j * A - A * skewImagGenerator i j =
      (Complex.I/2) • (B+C) := by
    dsimp [skewImagGenerator, B, C]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_add, add_mul, mul_add]
    abel
  rw [hr, hi, matrixFrobeniusSq_smul, matrixFrobeniusSq_smul]
  have hs := matrixFrobeniusSq_parallelogram B C
  norm_num [map_div₀, Complex.normSq_I] at *
  linarith

/-- Real skew-Hermitian Parseval generators have the same adjoint Casimir as
complex matrix units. This is a finite matrix identity, independent of any
manifold or heat-semigroup formalization. -/
theorem skew_generator_casimir {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    (∑ i, ∑ j,
      (matrixFrobeniusSq (skewRealGenerator i j * A - A * skewRealGenerator i j) +
        matrixFrobeniusSq (skewImagGenerator i j * A - A * skewImagGenerator i j))) =
      2 * Fintype.card ι * matrixFrobeniusSq A - 2 * Complex.normSq A.trace := by
  simp_rw [skew_generator_pair_commutator, ← Finset.sum_div, Finset.sum_add_distrib]
  have hswap : (∑ i : ι, ∑ j : ι, matrixFrobeniusSq
      (Matrix.single j i 1 * A - A * Matrix.single j i 1)) =
      ∑ i : ι, ∑ j : ι, matrixFrobeniusSq
      (Matrix.single i j 1 * A - A * Matrix.single i j 1) := Finset.sum_comm
  rw [hswap, matrix_unit_casimir]
  ring

/-- On trace-zero matrices the quarter-Casimir form has coefficient `n/2`, the
coefficient appearing in the Ricci curvature of the special unitary group. -/
theorem quarter_skew_casimir_traceless {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.trace = 0) :
    (1/4 : ℝ) * (∑ i, ∑ j,
      (matrixFrobeniusSq (skewRealGenerator i j * A - A * skewRealGenerator i j) +
        matrixFrobeniusSq (skewImagGenerator i j * A - A * skewImagGenerator i j))) =
      (Fintype.card ι : ℝ) / 2 * matrixFrobeniusSq A := by
  rw [skew_generator_casimir, hA]
  simp only [Complex.normSq_zero, mul_zero, sub_zero]
  ring


/-- The real Hilbert--Schmidt pairing, without a choice of ambient norm. -/
def matrixRealPair {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A B : Matrix ι κ ℂ) : ℝ := ∑ i, ∑ j, (conj (A i j) * B i j).re

theorem matrixRealPair_smul_left {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ℝ) (A B : Matrix ι κ ℂ) :
    matrixRealPair ((c : ℂ) • A) B = c * matrixRealPair A B := by
  simp only [matrixRealPair, Matrix.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal,
    mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Finset.mul_sum]

theorem matrixRealPair_add_left {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A B C : Matrix ι κ ℂ) :
    matrixRealPair (A+B) C = matrixRealPair A C + matrixRealPair B C := by
  simp [matrixRealPair, add_mul, Finset.sum_add_distrib]

theorem matrixRealPair_sub_left {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A B C : Matrix ι κ ℂ) :
    matrixRealPair (A-B) C = matrixRealPair A C - matrixRealPair B C := by
  simp [matrixRealPair, sub_mul, Finset.sum_sub_distrib]

theorem matrixRealPair_single_left {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (i : ι) (j : κ) (c : ℂ) (A : Matrix ι κ ℂ) :
    matrixRealPair (Matrix.single i j c) A = (conj c * A i j).re := by
  simp [matrixRealPair, Matrix.single, ite_and, apply_ite, ite_mul]

/-- On skew-Hermitian matrices the two frame coefficients are precisely the
real and imaginary matrix coordinates. -/
theorem skew_generator_realPair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : Aᴴ = -A) (i j : ι) :
    matrixRealPair (skewRealGenerator i j) A = (A i j).re ∧
      matrixRealPair (skewImagGenerator i j) A = (A i j).im := by
  have hij : conj (A j i) = -A i j := congrFun (congrFun hA i) j
  have hre := congrArg Complex.re hij
  have him := congrArg Complex.im hij
  simp only [Complex.conj_re, Complex.neg_re] at hre
  simp only [Complex.conj_im, Complex.neg_im] at him
  have hS : skewRealGenerator i j =
      Matrix.single i j (1/2 : ℂ) - Matrix.single j i (1/2 : ℂ) := by
    simp [skewRealGenerator, smul_sub, Matrix.smul_single]
  have hT : skewImagGenerator i j =
      Matrix.single i j (Complex.I/2) + Matrix.single j i (Complex.I/2) := by
    simp [skewImagGenerator, smul_add, Matrix.smul_single]
  rw [hS, hT, matrixRealPair_sub_left, matrixRealPair_add_left]
  simp only [matrixRealPair_single_left]
  norm_num [Complex.mul_re, Complex.div_re, Complex.div_im]
  constructor <;> linarith

/-- The ordered skew-Hermitian directions form a real Parseval frame. -/
theorem skew_generator_parseval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : Aᴴ = -A) :
    (∑ i, ∑ j, ((matrixRealPair (skewRealGenerator i j) A)^2 +
      (matrixRealPair (skewImagGenerator i j) A)^2)) = matrixFrobeniusSq A := by
  unfold matrixFrobeniusSq
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [(skew_generator_realPair A hA i j).1, (skew_generator_realPair A hA i j).2]
  simp [Complex.normSq_apply, pow_two]


/-- Orthogonal removal of the scalar trace direction. -/
def matrixTraceZeroPart {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  A - (A.trace / Fintype.card ι) • (1 : Matrix ι ι ℂ)

theorem matrixTraceZeroPart_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (A : Matrix ι ι ℂ) : (matrixTraceZeroPart A).trace = 0 := by
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [matrixTraceZeroPart, Matrix.trace_sub, Matrix.trace_smul, div_mul_cancel₀ _ hn]

theorem matrixTraceZeroPart_skew {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : Aᴴ = -A) :
    (matrixTraceZeroPart A)ᴴ = -matrixTraceZeroPart A := by
  have ht : star A.trace = -A.trace := by
    rw [← Matrix.trace_conjTranspose, hA, Matrix.trace_neg]
  simp only [matrixTraceZeroPart, Matrix.conjTranspose_sub, hA,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_div₀, star_natCast]
  rw [ht, neg_div, neg_smul]
  abel

theorem matrixTraceZeroPart_commutator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) :
    matrixTraceZeroPart A * B - B * matrixTraceZeroPart A = A*B-B*A := by
  simp only [matrixTraceZeroPart, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    one_mul, mul_one]
  abel

theorem matrixRealPair_scalar_one_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (A : Matrix ι ι ℂ) :
    matrixRealPair (c • (1 : Matrix ι ι ℂ)) A = (conj c * A.trace).re := by
  simp [matrixRealPair, Matrix.smul_apply, Matrix.one_apply, apply_ite,
    ite_mul, Matrix.trace, Finset.mul_sum, Complex.re_sum]

theorem matrixRealPair_traceZeroPart_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hB : B.trace = 0) :
    matrixRealPair (matrixTraceZeroPart A) B = matrixRealPair A B := by
  rw [matrixTraceZeroPart, matrixRealPair_sub_left, matrixRealPair_scalar_one_left, hB]
  simp

/-- Removing the central direction yields a Parseval frame on the trace-zero
skew-Hermitian Lie algebra. -/
theorem traceless_skew_generator_parseval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : Aᴴ = -A) (htr : A.trace = 0) :
    (∑ i, ∑ j, ((matrixRealPair (matrixTraceZeroPart (skewRealGenerator i j)) A)^2 +
      (matrixRealPair (matrixTraceZeroPart (skewImagGenerator i j)) A)^2)) =
      matrixFrobeniusSq A := by
  simp_rw [matrixRealPair_traceZeroPart_left _ A htr]
  exact skew_generator_parseval A hA

/-- The quarter-Casimir identity holds using only trace-zero skew-Hermitian
directions, with no contribution from the central direction. -/
theorem quarter_traceless_skew_casimir {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (htr : A.trace = 0) :
    (1/4 : ℝ) * (∑ i, ∑ j,
      (matrixFrobeniusSq
        (matrixTraceZeroPart (skewRealGenerator i j) * A -
          A * matrixTraceZeroPart (skewRealGenerator i j)) +
        matrixFrobeniusSq
        (matrixTraceZeroPart (skewImagGenerator i j) * A -
          A * matrixTraceZeroPart (skewImagGenerator i j)))) =
      (Fintype.card ι : ℝ) / 2 * matrixFrobeniusSq A := by
  simp_rw [matrixTraceZeroPart_commutator]
  exact quarter_skew_casimir_traceless A htr

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2CasimirBracket -/
section
open scoped Matrix BigOperators ComplexConjugate

namespace BosonicLearn.Prop2
noncomputable section

theorem matrixRealPair_symm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A B : Matrix ι κ ℂ) : matrixRealPair A B = matrixRealPair B A := by
  unfold matrixRealPair
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem matrixRealPair_eq_trace {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ) : matrixRealPair A B = (Aᴴ * B).trace.re := by
  simp only [matrixRealPair, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.star_def, Complex.re_sum]
  exact Finset.sum_comm

/-- Invariance of the real Hilbert--Schmidt pairing under the infinitesimal
unitary action. -/
theorem matrixRealPair_commutator {ι : Type*} [Fintype ι]
    (A B C : Matrix ι ι ℂ) (hB : Bᴴ = -B) :
    matrixRealPair A (B*C-C*B) = matrixRealPair (A*B-B*A) C := by
  rw [matrixRealPair_eq_trace, matrixRealPair_eq_trace]
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hB,
    neg_mul, mul_neg, sub_neg_eq_add, neg_add_eq_sub, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle Aᴴ C B]

theorem commutator_skew {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ) (hA : Aᴴ = -A) (hB : Bᴴ = -B) :
    (A*B-B*A)ᴴ = -(A*B-B*A) := by
  simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hA, hB]

theorem commutator_trace {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ) : (A*B-B*A).trace = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm A B, sub_self]

/-- A finite index for the projected real and imaginary matrix-unit directions. -/
abbrev SpecialUnitaryFrameIndex (ι : Type*) := (ι × ι) × Bool

def specialUnitaryFrame {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : SpecialUnitaryFrameIndex ι) : Matrix ι ι ℂ :=
  matrixTraceZeroPart (if a.2 then skewImagGenerator a.1.1 a.1.2
    else skewRealGenerator a.1.1 a.1.2)

theorem specialUnitaryFrame_skew {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : SpecialUnitaryFrameIndex ι) :
    (specialUnitaryFrame a)ᴴ = -specialUnitaryFrame a := by
  apply matrixTraceZeroPart_skew
  split
  · exact skewImagGenerator_conjTranspose _ _
  · exact skewRealGenerator_conjTranspose _ _

theorem specialUnitaryFrame_trace {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a : SpecialUnitaryFrameIndex ι) : (specialUnitaryFrame a).trace = 0 :=
  matrixTraceZeroPart_trace _

theorem specialUnitaryFrame_parseval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : Aᴴ = -A) (htr : A.trace = 0) :
    (∑ a : SpecialUnitaryFrameIndex ι, (matrixRealPair (specialUnitaryFrame a) A)^2) =
      matrixFrobeniusSq A := by
  have h := traceless_skew_generator_parseval A hA htr
  simpa [specialUnitaryFrame, Fintype.sum_prod_type, Fintype.sum_bool, add_comm] using h

theorem specialUnitaryFrame_casimir {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (htr : A.trace = 0) :
    (∑ a : SpecialUnitaryFrameIndex ι,
      matrixFrobeniusSq (specialUnitaryFrame a * A - A * specialUnitaryFrame a)) =
      2 * Fintype.card ι * matrixFrobeniusSq A := by
  have h := quarter_traceless_skew_casimir A htr
  have he : (∑ a : SpecialUnitaryFrameIndex ι,
      matrixFrobeniusSq (specialUnitaryFrame a * A - A * specialUnitaryFrame a)) =
      ∑ i, ∑ j,
        (matrixFrobeniusSq (matrixTraceZeroPart (skewRealGenerator i j) * A -
          A * matrixTraceZeroPart (skewRealGenerator i j)) +
        matrixFrobeniusSq (matrixTraceZeroPart (skewImagGenerator i j) * A -
          A * matrixTraceZeroPart (skewImagGenerator i j))) := by
    simp [specialUnitaryFrame, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  rw [he]
  linarith

/-- The scalar commutator-frame square identity needed by the algebraic Bochner
argument. It gives the exact curvature coefficient `n/2` after division by four. -/
theorem specialUnitaryFrame_commutator_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix ι ι ℂ) (hV : Vᴴ = -V) (htr : V.trace = 0) :
    (∑ a : SpecialUnitaryFrameIndex ι, ∑ b : SpecialUnitaryFrameIndex ι,
      (matrixRealPair V (specialUnitaryFrame a * specialUnitaryFrame b -
        specialUnitaryFrame b * specialUnitaryFrame a))^2) =
      2 * Fintype.card ι * matrixFrobeniusSq V := by
  have hinner (a : SpecialUnitaryFrameIndex ι) :
      (∑ b : SpecialUnitaryFrameIndex ι,
        (matrixRealPair V (specialUnitaryFrame a * specialUnitaryFrame b -
          specialUnitaryFrame b * specialUnitaryFrame a))^2) =
      matrixFrobeniusSq (V * specialUnitaryFrame a - specialUnitaryFrame a * V) := by
    simp_rw [matrixRealPair_commutator V _ _ (specialUnitaryFrame_skew a)]
    simp_rw [matrixRealPair_symm (V * specialUnitaryFrame a - specialUnitaryFrame a * V)]
    exact specialUnitaryFrame_parseval _
      (commutator_skew V _ hV (specialUnitaryFrame_skew a)) (commutator_trace V _)
  simp_rw [hinner]
  have hnorm (a : SpecialUnitaryFrameIndex ι) :
      matrixFrobeniusSq (V * specialUnitaryFrame a - specialUnitaryFrame a * V) =
      matrixFrobeniusSq (specialUnitaryFrame a * V - V * specialUnitaryFrame a) := by
    simp [matrixFrobeniusSq, Complex.normSq_sub, add_comm, Complex.mul_re]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hnorm]
  exact specialUnitaryFrame_casimir V htr

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2CasimirCentral -/
section
open scoped BigOperators

namespace BosonicLearn.Prop2
noncomputable section

/-- The sum of squares of a finite family of operators commutes with every
member when its bracket coefficients are skew in the two frame coordinates.
This is the algebraic centrality of the quadratic Casimir. -/
theorem sum_squares_commute_of_structure_constants
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (D : ι → Module.End ℝ V) (c : ι → ι → ι → ℝ)
    (hskew : ∀ k i j, c k i j = -c k j i)
    (hbracket : ∀ k i, D k * D i - D i * D k = ∑ j, c k i j • D j)
    (k : ι) :
    D k * (∑ i, D i * D i) = (∑ i, D i * D i) * D k := by
  have hterm (i : ι) : D k * (D i * D i) - (D i * D i) * D k =
      (D k * D i - D i * D k) * D i + D i * (D k * D i - D i * D k) := by
    noncomm_ring
  have hc : D k * (∑ i, D i * D i) - (∑ i, D i * D i) * D k =
      ∑ i, ∑ j, c k i j • (D j * D i + D i * D j) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp_rw [hterm, hbracket, Finset.sum_mul, Finset.mul_sum,
      smul_mul_assoc, mul_smul_comm, ← Finset.sum_add_distrib, ← smul_add]
  have hz : (∑ i, ∑ j, c k i j • (D j * D i + D i * D j)) = 0 := by
    let S := ∑ i, ∑ j, c k i j • (D j * D i + D i * D j)
    have he : S = -S := by
      calc
        S = ∑ j, ∑ i, c k i j • (D j * D i + D i * D j) := Finset.sum_comm
        _ = ∑ i, ∑ j, -(c k i j • (D j * D i + D i * D j)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          calc
            c k j i • (D i * D j + D j * D i) =
                (-c k i j) • (D i * D j + D j * D i) := by rw [hskew k j i]
            _ = _ := by rw [neg_smul, add_comm]
        _ = -S := by simp only [S, Finset.sum_neg_distrib]
    have hs : (2 : ℝ) • S = 0 := by rw [two_smul]; exact eq_neg_iff_add_eq_zero.mp he
    exact (smul_eq_zero.mp hs).resolve_left (by norm_num)
  rw [hz] at hc
  exact sub_eq_zero.mp hc

/-- Pointwise form for linear differential operators on a smooth test-function
algebra. It matches the commutation premise of the algebraic Bochner identity. -/
theorem sum_squares_apply_commute_of_structure_constants
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (D : ι → Module.End ℝ V) (c : ι → ι → ι → ℝ)
    (hskew : ∀ k i j, c k i j = -c k j i)
    (hbracket : ∀ k i f, D k (D i f) - D i (D k f) = ∑ j, c k i j • D j f)
    (k : ι) (f : V) :
    D k (∑ i, D i (D i f)) = ∑ i, D i (D i (D k f)) := by
  have hb (k i : ι) : D k * D i - D i * D k = ∑ j, c k i j • D j := by
    ext f
    simpa using hbracket k i f
  have h := congrArg (fun A : Module.End ℝ V => A f)
    (sum_squares_commute_of_structure_constants D c hskew hb k)
  simpa using h

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2CasimirStructure -/
section
open scoped Matrix BigOperators ComplexConjugate

namespace BosonicLearn.Prop2
noncomputable section

theorem matrixRealPair_self {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) : matrixRealPair A A = matrixFrobeniusSq A := by
  simp [matrixRealPair, matrixFrobeniusSq, Complex.mul_re, Complex.normSq_apply]

theorem matrixFrobeniusSq_eq_zero_iff {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) : matrixFrobeniusSq A = 0 ↔ A = 0 := by
  classical
  constructor
  · intro h
    ext i j
    have hrow : Complex.normSq (A i j) ≤ ∑ b, Complex.normSq (A i b) :=
      Finset.single_le_sum (fun b _ => Complex.normSq_nonneg (A i b)) (Finset.mem_univ j)
    have htotal : (∑ b, Complex.normSq (A i b)) ≤ matrixFrobeniusSq A :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => Complex.normSq_nonneg (A a b)))
        (Finset.mem_univ i)
    have hz : Complex.normSq (A i j) = 0 := le_antisymm (hrow.trans (htotal.trans_eq h))
      (Complex.normSq_nonneg _)
    exact Complex.normSq_eq_zero.mp hz
  · rintro rfl
    simp [matrixFrobeniusSq]

theorem matrixRealPair_sum_left {ι κ : Type*} [Fintype ι]
    (s : Finset κ) (f : κ → Matrix ι ι ℂ) (B : Matrix ι ι ℂ) :
    matrixRealPair (∑ a ∈ s, f a) B = ∑ a ∈ s, matrixRealPair (f a) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [matrixRealPair]
  | @insert a s ha ih => simp [Finset.sum_insert, ha, matrixRealPair_add_left, ih]

/-- Polarization of the explicit Parseval coordinates. -/
theorem specialUnitaryFrame_parseval_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hA : Aᴴ = -A) (hB : Bᴴ = -B)
    (htrA : A.trace = 0) (htrB : B.trace = 0) :
    (∑ a : SpecialUnitaryFrameIndex ι,
      matrixRealPair (specialUnitaryFrame a) A * matrixRealPair (specialUnitaryFrame a) B) =
      matrixRealPair A B := by
  simp only [specialUnitaryFrame, Fintype.sum_prod_type, Fintype.sum_bool,
    Bool.false_eq_true, if_false, if_true]
  simp_rw [matrixRealPair_traceZeroPart_left _ A htrA,
    matrixRealPair_traceZeroPart_left _ B htrB,
    (skew_generator_realPair A hA _ _).1, (skew_generator_realPair A hA _ _).2,
    (skew_generator_realPair B hB _ _).1, (skew_generator_realPair B hB _ _).2]
  simp [matrixRealPair, Complex.mul_re, add_comm]

/-- The Parseval frame reconstructs every trace-zero skew-Hermitian matrix. -/
theorem specialUnitaryFrame_reconstruct {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (hA : Aᴴ = -A) (htr : A.trace = 0) :
    (∑ a : SpecialUnitaryFrameIndex ι,
      (matrixRealPair (specialUnitaryFrame a) A : ℂ) • specialUnitaryFrame a) = A := by
  let R : Matrix ι ι ℂ := ∑ a : SpecialUnitaryFrameIndex ι,
    (matrixRealPair (specialUnitaryFrame a) A : ℂ) • specialUnitaryFrame a
  have hR : Rᴴ = -R := by
    dsimp only [R]
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Complex.star_def,
      Complex.conj_ofReal, specialUnitaryFrame_skew, smul_neg, Finset.sum_neg_distrib]
  have hRt : R.trace = 0 := by
    simp [R, Matrix.trace_sum, Matrix.trace_smul, specialUnitaryFrame_trace]
  have hp (B : Matrix ι ι ℂ) (hB : Bᴴ = -B) (hBt : B.trace = 0) :
      matrixRealPair R B = matrixRealPair A B := by
    dsimp only [R]
    rw [matrixRealPair_sum_left]
    simp_rw [matrixRealPair_smul_left]
    exact specialUnitaryFrame_parseval_pair A B hA hB htr hBt
  have hD : (A-R)ᴴ = -(A-R) := by
    simp only [Matrix.conjTranspose_sub, hA, hR]
    abel
  have hDt : (A-R).trace = 0 := by simp [Matrix.trace_sub, htr, hRt]
  have hz : matrixFrobeniusSq (A-R) = 0 := by
    rw [← matrixRealPair_self, matrixRealPair_sub_left, hp (A-R) hD hDt, sub_self]
  exact (sub_eq_zero.mp ((matrixFrobeniusSq_eq_zero_iff _).mp hz)).symm

/-- Structure constants of the actual trace-zero skew-Hermitian Parseval frame. -/
def specialUnitaryStructure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b c : SpecialUnitaryFrameIndex ι) : ℝ :=
  matrixRealPair (specialUnitaryFrame c)
    (specialUnitaryFrame a * specialUnitaryFrame b - specialUnitaryFrame b * specialUnitaryFrame a)

theorem specialUnitaryStructure_skew {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b c : SpecialUnitaryFrameIndex ι) :
    specialUnitaryStructure a b c = -specialUnitaryStructure a c b := by
  unfold specialUnitaryStructure
  rw [matrixRealPair_commutator _ _ _ (specialUnitaryFrame_skew a)]
  rw [matrixRealPair_symm (specialUnitaryFrame c * specialUnitaryFrame a -
    specialUnitaryFrame a * specialUnitaryFrame c)]
  simp only [matrixRealPair, Matrix.sub_apply, mul_sub, Complex.sub_re,
    Finset.sum_sub_distrib]
  ring

theorem specialUnitaryFrame_bracket_expansion {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a b : SpecialUnitaryFrameIndex ι) :
    specialUnitaryFrame a * specialUnitaryFrame b - specialUnitaryFrame b * specialUnitaryFrame a =
      ∑ c : SpecialUnitaryFrameIndex ι,
        (specialUnitaryStructure a b c : ℂ) • specialUnitaryFrame c := by
  exact (specialUnitaryFrame_reconstruct _
    (commutator_skew _ _ (specialUnitaryFrame_skew a) (specialUnitaryFrame_skew b))
    (commutator_trace _ _)).symm

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2FrameGradient -/
section
open scoped Matrix BigOperators ComplexConjugate

namespace BosonicLearn.Prop2
noncomputable section

theorem complex_ofReal_smul_matrix {ι κ : Type*} (c : ℝ) (A : Matrix ι κ ℂ) :
    (c : ℂ) • A = c • A := by
  ext i j
  exact (Complex.real_smul).symm

theorem specialUnitaryFrame_reconstruct_real {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (hA : Aᴴ = -A) (htr : A.trace = 0) :
    (∑ a : SpecialUnitaryFrameIndex ι,
      matrixRealPair (specialUnitaryFrame a) A • specialUnitaryFrame a) = A := by
  simpa only [complex_ofReal_smul_matrix] using specialUnitaryFrame_reconstruct A hA htr

/-- A real linear functional on the traceless skew-Hermitian tangent space has
frame energy bounded by the square of its Hilbert--Schmidt dual bound. -/
theorem specialUnitaryFrame_energy_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ell : (Matrix ι ι ℂ) →ₗ[ℝ] ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ B : Matrix ι ι ℂ, Bᴴ = -B → B.trace = 0 →
      |ell B| ≤ L * Real.sqrt (matrixFrobeniusSq B)) :
    (∑ a : SpecialUnitaryFrameIndex ι, (ell (specialUnitaryFrame a))^2) ≤ L^2 := by
  let R : Matrix ι ι ℂ := ∑ a : SpecialUnitaryFrameIndex ι,
    ell (specialUnitaryFrame a) • specialUnitaryFrame a
  have hR : Rᴴ = -R := by
    dsimp only [R]
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial,
      specialUnitaryFrame_skew, smul_neg, Finset.sum_neg_distrib]
  have hRt : R.trace = 0 := by
    simp [R, Matrix.trace_sum, Matrix.trace_smul, specialUnitaryFrame_trace]
  have hpair (B : Matrix ι ι ℂ) (hB : Bᴴ = -B) (hBt : B.trace = 0) :
      matrixRealPair R B = ell B := by
    dsimp only [R]
    rw [matrixRealPair_sum_left]
    simp_rw [← complex_ofReal_smul_matrix, matrixRealPair_smul_left]
    have h := congrArg ell (specialUnitaryFrame_reconstruct_real B hB hBt)
    simp only [map_sum, map_smul, smul_eq_mul] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have henergy : ell R = ∑ a : SpecialUnitaryFrameIndex ι, (ell (specialUnitaryFrame a))^2 := by
    simp [R, pow_two]
  have hnorm : matrixFrobeniusSq R = ∑ a : SpecialUnitaryFrameIndex ι,
      (ell (specialUnitaryFrame a))^2 := by
    rw [← matrixRealPair_self, hpair R hR hRt, henergy]
  have hb := hbound R hR hRt
  rw [henergy, hnorm] at hb
  have hnonneg : 0 ≤ ∑ a : SpecialUnitaryFrameIndex ι, (ell (specialUnitaryFrame a))^2 :=
    Finset.sum_nonneg (fun a _ => sq_nonneg _)
  rw [abs_of_nonneg hnonneg] at hb
  have hs := Real.sq_sqrt hnonneg
  have hs0 := Real.sqrt_nonneg (∑ a : SpecialUnitaryFrameIndex ι, (ell (specialUnitaryFrame a))^2)
  have hroot : Real.sqrt (∑ a : SpecialUnitaryFrameIndex ι, (ell (specialUnitaryFrame a))^2) ≤ L := by
    by_contra h
    have hlt := lt_of_not_ge h
    have hp := mul_pos (sub_pos.mpr hlt) (hL.trans_lt hlt)
    nlinarith
  have hsq := pow_le_pow_left₀ hs0 hroot 2
  rwa [hs] at hsq

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2FrameFunctional -/
section
open scoped Matrix BigOperators

namespace BosonicLearn.Prop2
noncomputable section

def specialUnitaryFrameGradient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ell : (Matrix ι ι ℂ) →ₗ[ℝ] ℝ) : Matrix ι ι ℂ :=
  ∑ a : SpecialUnitaryFrameIndex ι, ell (specialUnitaryFrame a) • specialUnitaryFrame a

theorem specialUnitaryFrameGradient_skew {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ell : (Matrix ι ι ℂ) →ₗ[ℝ] ℝ) :
    (specialUnitaryFrameGradient ell)ᴴ = -specialUnitaryFrameGradient ell := by
  simp only [specialUnitaryFrameGradient, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    star_trivial, specialUnitaryFrame_skew, smul_neg, Finset.sum_neg_distrib]

theorem specialUnitaryFrameGradient_trace {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ell : (Matrix ι ι ℂ) →ₗ[ℝ] ℝ) : (specialUnitaryFrameGradient ell).trace = 0 := by
  simp [specialUnitaryFrameGradient, Matrix.trace_sum, Matrix.trace_smul, specialUnitaryFrame_trace]

theorem specialUnitaryFrameGradient_represents {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ell : (Matrix ι ι ℂ) →ₗ[ℝ] ℝ) (B : Matrix ι ι ℂ)
    (hB : Bᴴ = -B) (hBt : B.trace = 0) :
    matrixRealPair (specialUnitaryFrameGradient ell) B = ell B := by
  rw [specialUnitaryFrameGradient, matrixRealPair_sum_left]
  simp_rw [← complex_ofReal_smul_matrix, matrixRealPair_smul_left]
  have h := congrArg ell (specialUnitaryFrame_reconstruct_real B hB hBt)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem specialUnitaryFrameGradient_energy {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ell : (Matrix ι ι ℂ) →ₗ[ℝ] ℝ) :
    matrixFrobeniusSq (specialUnitaryFrameGradient ell) =
      ∑ a : SpecialUnitaryFrameIndex ι, (ell (specialUnitaryFrame a))^2 := by
  rw [← matrixRealPair_self, specialUnitaryFrameGradient_represents ell _
    (specialUnitaryFrameGradient_skew ell) (specialUnitaryFrameGradient_trace ell)]
  simp [specialUnitaryFrameGradient, pow_two]

/-- The Casimir curvature identity for an arbitrary real differential. -/
theorem specialUnitaryFrame_functional_commutator_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (ell : (Matrix ι ι ℂ) →ₗ[ℝ] ℝ) :
    (∑ a : SpecialUnitaryFrameIndex ι, ∑ b : SpecialUnitaryFrameIndex ι,
      (ell (specialUnitaryFrame a * specialUnitaryFrame b -
        specialUnitaryFrame b * specialUnitaryFrame a))^2) =
      2 * Fintype.card ι * (∑ a : SpecialUnitaryFrameIndex ι, (ell (specialUnitaryFrame a))^2) := by
  have h := specialUnitaryFrame_commutator_sq (specialUnitaryFrameGradient ell)
    (specialUnitaryFrameGradient_skew ell) (specialUnitaryFrameGradient_trace ell)
  simp_rw [specialUnitaryFrameGradient_represents ell _
    (commutator_skew _ _ (specialUnitaryFrame_skew _) (specialUnitaryFrame_skew _))
    (commutator_trace _ _)] at h
  rw [specialUnitaryFrameGradient_energy] at h
  exact h

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2PeakApproximation -/
section
open MeasureTheory MeasureTheory.Measure Filter Set TopologicalSpace
open scoped Topology

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 800000

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MetrizableSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsFiniteMeasure μ] [IsOpenPosMeasure μ]

/-- Right translates of a continuous function, continuously parameterized in the
uniform norm. This permits a single Banach-valued peak-function argument to prove
uniform approximation on the whole compact group. -/
def rightTranslateFamily (F : C(G, ℝ)) : C(G, C(G, ℝ)) :=
  ContinuousMap.curry ⟨fun p : G × G => F (p.2 * p.1),
    F.continuous.comp (continuous_snd.mul continuous_fst)⟩

@[simp] theorem rightTranslateFamily_apply (F : C(G, ℝ)) (V U : G) :
    rightTranslateFamily F V U = F (U * V) := rfl

@[simp] theorem rightTranslateFamily_one (F : C(G, ℝ)) :
    rightTranslateFamily F 1 = F := by ext U; simp

/-- Convolution with a normalized positive power of a peak function. -/
def peakConvolution (c : C(G, ℝ)) (m : ℕ) (F : C(G, ℝ)) : C(G, ℝ) :=
  (∫ V, c V ^ m ∂μ)⁻¹ • ∫ V, c V ^ m • rightTranslateFamily F V ∂μ

theorem continuous_integrable_compact {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : G → E) (hf : Continuous f) : Integrable f μ := by
  simpa only [IntegrableOn, Measure.restrict_univ] using
    hf.continuousOn.integrableOn_compact (μ := μ) isCompact_univ

theorem peakConvolution_apply (c : C(G, ℝ)) (m : ℕ) (F : C(G, ℝ)) (U : G) :
    peakConvolution μ c m F U =
      (∫ V, c V ^ m ∂μ)⁻¹ * ∫ V, c V ^ m * F (U * V) ∂μ := by
  change ((∫ V, c V ^ m ∂μ)⁻¹ •
    ∫ V, c V ^ m • rightTranslateFamily F V ∂μ) U = _
  rw [ContinuousMap.smul_apply, ContinuousMap.integral_apply]
  · rfl
  · exact continuous_integrable_compact μ _
      ((c.continuous.pow m).smul (rightTranslateFamily F).continuous)

/-- Haar reparametrization puts all dependence on U in the peak kernel. In a
matrix group this turns polynomial peak kernels into polynomial approximants. -/
theorem peakConvolution_apply_reparam [IsMulLeftInvariant μ]
    (c : C(G, ℝ)) (m : ℕ) (F : C(G, ℝ)) (U : G) :
    peakConvolution μ c m F U =
      (∫ V, c V ^ m ∂μ)⁻¹ * ∫ W, c (U⁻¹ * W) ^ m * F W ∂μ := by
  rw [peakConvolution_apply]
  congr 1
  have h := integral_mul_left_eq_self (μ := μ)
    (fun W => c (U⁻¹ * W) ^ m * F W) U
  simpa only [inv_mul_cancel_left] using h

/-- The reparametrized kernel, viewed as a continuous function of U and varying
continuously in W in the uniform norm. -/
def peakKernelFamily (c : C(G, ℝ)) (m : ℕ) : C(G, C(G, ℝ)) :=
  ContinuousMap.curry ⟨fun p : G × G => c (p.2⁻¹ * p.1) ^ m,
    (c.continuous.comp (continuous_snd.inv.mul continuous_fst)).pow m⟩

@[simp] theorem peakKernelFamily_apply (c : C(G, ℝ)) (m : ℕ) (W U : G) :
    peakKernelFamily c m W U = c (U⁻¹ * W) ^ m := rfl

theorem peakConvolution_eq_integral_kernel [IsMulLeftInvariant μ]
    (c : C(G, ℝ)) (m : ℕ) (F : C(G, ℝ)) :
    peakConvolution μ c m F =
      (∫ V, c V ^ m ∂μ)⁻¹ • ∫ W, F W • peakKernelFamily c m W ∂μ := by
  ext U
  rw [peakConvolution_apply_reparam, ContinuousMap.smul_apply, ContinuousMap.integral_apply]
  · simp only [ContinuousMap.smul_apply, peakKernelFamily_apply, smul_eq_mul]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun W => mul_comm _ _
  · exact continuous_integrable_compact μ _
      (F.continuous.smul (peakKernelFamily c m).continuous)

/-- Once every translated kernel belongs to a fixed finite-dimensional function
space, averaging preserves membership. This avoids expanding its coefficients
under the integral. -/
theorem peakConvolution_mem_of_kernels_mem [IsProbabilityMeasure μ] [IsMulLeftInvariant μ]
    (P : Submodule ℝ C(G, ℝ)) [FiniteDimensional ℝ P]
    (c : C(G, ℝ)) (m : ℕ) (F : C(G, ℝ))
    (hkernel : ∀ W, peakKernelFamily c m W ∈ P) : peakConvolution μ c m F ∈ P := by
  rw [peakConvolution_eq_integral_kernel]
  apply P.smul_mem
  exact P.convex.integral_mem P.closed_of_finiteDimensional
    (Filter.Eventually.of_forall fun W => P.smul_mem (F W) (hkernel W))
    (continuous_integrable_compact μ _ (F.continuous.smul (peakKernelFamily c m).continuous))

theorem peak_power_integral_pos (c : C(G, ℝ)) (hc : ∀ V, 0 ≤ c V)
    (hc1 : 0 < c 1) (m : ℕ) : 0 < ∫ V, c V ^ m ∂μ := by
  exact integral_pos_of_integrable_nonneg_nonzero (c.continuous.pow m)
    (continuous_integrable_compact μ _ (c.continuous.pow m))
    (fun V => pow_nonneg (hc V) m) (pow_pos hc1 m).ne'

theorem peakConvolution_const (c : C(G, ℝ)) (hc : ∀ V, 0 ≤ c V)
    (hc1 : 0 < c 1) (m : ℕ) (b : ℝ) :
    peakConvolution μ c m (ContinuousMap.const G b) = ContinuousMap.const G b := by
  ext U
  rw [peakConvolution_apply]
  simp only [ContinuousMap.const_apply, integral_mul_const]
  rw [← mul_assoc, inv_mul_cancel₀ (peak_power_integral_pos μ c hc hc1 m).ne', one_mul]

theorem peakConvolution_mono (c : C(G, ℝ)) (hc : ∀ V, 0 ≤ c V)
    (hc1 : 0 < c 1) (m : ℕ) (F H : C(G, ℝ)) (hFH : ∀ U, F U ≤ H U) (U : G) :
    peakConvolution μ c m F U ≤ peakConvolution μ c m H U := by
  rw [peakConvolution_apply, peakConvolution_apply]
  apply mul_le_mul_of_nonneg_left _
    (inv_nonneg.mpr (peak_power_integral_pos μ c hc hc1 m).le)
  apply integral_mono
  · exact continuous_integrable_compact μ _
      ((c.continuous.pow m).mul (F.continuous.comp (continuous_const.mul continuous_id)))
  · exact continuous_integrable_compact μ _
      ((c.continuous.pow m).mul (H.continuous.comp (continuous_const.mul continuous_id)))
  · intro V
    exact mul_le_mul_of_nonneg_left (hFH (U * V)) (pow_nonneg (hc V) m)

/-- In particular, positive lower bounds and upper bounds survive approximation. -/
theorem peakConvolution_mem_Icc (c : C(G, ℝ)) (hc : ∀ V, 0 ≤ c V)
    (hc1 : 0 < c 1) (m : ℕ) (F : C(G, ℝ)) (a b : ℝ)
    (hF : ∀ U, F U ∈ Icc a b) (U : G) : peakConvolution μ c m F U ∈ Icc a b := by
  have hlo := peakConvolution_mono μ c hc hc1 m (ContinuousMap.const G a) F
    (fun U => (hF U).1) U
  have hup := peakConvolution_mono μ c hc hc1 m F (ContinuousMap.const G b)
    (fun U => (hF U).2) U
  rw [peakConvolution_const μ c hc hc1] at hlo hup
  exact ⟨hlo, hup⟩

/-- Normalized powers of any nonnegative continuous function with its unique
maximum at the identity approximate every continuous function uniformly. -/
theorem peakConvolution_tendsto (c : C(G, ℝ)) (hc : ∀ V, 0 ≤ c V)
    (hc1 : 0 < c 1) (hpeak : ∀ V, V ≠ 1 → c V < c 1) (F : C(G, ℝ)) :
    Tendsto (fun m : ℕ => peakConvolution μ c m F) atTop (𝓝 F) := by
  have h := tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn
    (μ := μ) (g := rightTranslateFamily F) (x₀ := (1 : G)) isCompact_univ
    c.continuous.continuousOn (fun V _ hV => hpeak V hV) (fun V _ => hc V) hc1
    (by simp) (rightTranslateFamily F).continuous.continuousOn
  simpa only [Measure.restrict_univ, rightTranslateFamily_one, peakConvolution] using h

/-- Averaging preserves every bound on differences that is uniform under right
translation. Applying this with a right-invariant distance preserves Lipschitz
constants exactly. -/
theorem peakConvolution_abs_sub_le (c : C(G, ℝ)) (hc : ∀ V, 0 ≤ c V)
    (hc1 : 0 < c 1) (m : ℕ) (F : C(G, ℝ)) (U V : G) (B : ℝ)
    (hB : ∀ W, |F (U * W) - F (V * W)| ≤ B) :
    |peakConvolution μ c m F U - peakConvolution μ c m F V| ≤ B := by
  have hpos := peak_power_integral_pos μ c hc hc1 m
  have hi (U : G) : Integrable (fun W => c W ^ m * F (U * W)) μ :=
    continuous_integrable_compact μ _
      ((c.continuous.pow m).mul (F.continuous.comp (continuous_const.mul continuous_id)))
  have ha : Integrable (fun W => c W ^ m * |F (U * W) - F (V * W)|) μ :=
    continuous_integrable_compact μ _
      ((c.continuous.pow m).mul
        ((F.continuous.comp (continuous_const.mul continuous_id)).sub
          (F.continuous.comp (continuous_const.mul continuous_id))).abs)
  have hb : Integrable (fun W => c W ^ m * B) μ :=
    (continuous_integrable_compact μ _ (c.continuous.pow m)).mul_const B
  rw [peakConvolution_apply, peakConvolution_apply, ← mul_sub, ← integral_sub (hi U) (hi V),
    abs_mul, abs_of_pos (inv_pos.mpr hpos)]
  calc
    _ ≤ (∫ W, c W ^ m ∂μ)⁻¹ * ∫ W, |c W ^ m * F (U * W) - c W ^ m * F (V * W)| ∂μ :=
      mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs) (inv_nonneg.mpr hpos.le)
    _ = (∫ W, c W ^ m ∂μ)⁻¹ * ∫ W, c W ^ m * |F (U * W) - F (V * W)| ∂μ := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun W => by
        dsimp only
        rw [← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg (hc W) m)]
    _ ≤ (∫ W, c W ^ m ∂μ)⁻¹ * ∫ W, c W ^ m * B ∂μ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hpos.le)
      apply integral_mono ha hb
      intro W
      exact mul_le_mul_of_nonneg_left (hB W) (pow_nonneg (hc W) m)
    _ = B := by rw [integral_mul_const, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2SpecialUnitaryPeak -/
section
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology Matrix Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 800000

theorem specialUnitary_trace_re_abs_le (n : ℕ) (hn : 1 ≤ n)
    (U : Matrix.specialUnitaryGroup (Fin n) ℂ) :
    |(U : Matrix (Fin n) (Fin n) ℂ).trace.re| ≤ n := by
  letI : NeZero n := ⟨by omega⟩
  have hnorm : ‖(U : Matrix (Fin n) (Fin n) ℂ)‖ = 1 :=
    CStarRing.norm_of_mem_unitary U.property.1
  calc
    _ ≤ ‖(U : Matrix (Fin n) (Fin n) ℂ).trace‖ := Complex.abs_re_le_norm _
    _ ≤ n * ‖(U : Matrix (Fin n) (Fin n) ℂ)‖ := Prop5.matrix_trace_le_operator_norm _
    _ = n := by rw [hnorm, mul_one]

theorem specialUnitary_schatten_sub_one_sq (n : ℕ)
    (U : Matrix.specialUnitaryGroup (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 2
      ((U : Matrix (Fin n) (Fin n) ℂ) - 1) ^ 2 =
      2 * n - 2 * (U : Matrix (Fin n) (Fin n) ℂ).trace.re := by
  have hU := Matrix.mem_unitaryGroup_iff'.mp U.property.1
  rw [Matrix.star_eq_conjTranspose] at hU
  rw [Prop5.schatten_two_sq_eq_trace]
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.sub_mul,
    Matrix.mul_sub, mul_one, one_mul, hU, Matrix.trace_sub,
    Matrix.trace_one, Matrix.trace_conjTranspose, Complex.sub_re, Complex.star_def,
    Complex.conj_re, Complex.natCast_re, Fintype.card_fin]
  ring

theorem specialUnitary_trace_re_eq_dim_iff (n : ℕ)
    (U : Matrix.specialUnitaryGroup (Fin n) ℂ) :
    (U : Matrix (Fin n) (Fin n) ℂ).trace.re = n ↔ U = 1 := by
  constructor
  · intro h
    have hs := specialUnitary_schatten_sub_one_sq n U
    rw [h] at hs
    have hz : WHMultiplicativity.schattenNorm 2
        ((U : Matrix (Fin n) (Fin n) ℂ) - 1) = 0 := by nlinarith [sq_nonneg (0 : ℝ)]
    rw [← Prop5.norm_frobeniusMatrixEquiv, norm_eq_zero] at hz
    have hzero : (U : Matrix (Fin n) (Fin n) ℂ) - 1 = 0 :=
      (Prop5.frobeniusMatrixEquiv n).injective (by simpa using hz)
    exact Subtype.ext (sub_eq_zero.mp hzero)
  · rintro rfl
    simp

/-- A polynomial peak on SU(n), attaining one only at the identity. -/
def specialUnitaryPeak (n : ℕ) : C(Matrix.specialUnitaryGroup (Fin n) ℂ, ℝ) where
  toFun U := (1 + (U : Matrix (Fin n) (Fin n) ℂ).trace.re / n) / 2
  continuous_toFun := by fun_prop

theorem specialUnitaryPeak_mem_Icc (n : ℕ) (hn : 1 ≤ n)
    (U : Matrix.specialUnitaryGroup (Fin n) ℂ) : specialUnitaryPeak n U ∈ Icc 0 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := abs_le.mp (specialUnitary_trace_re_abs_le n hn U)
  have hl : -(1 : ℝ) ≤ (U : Matrix (Fin n) (Fin n) ℂ).trace.re / n :=
    (le_div_iff₀ hn0).mpr (by nlinarith [h.1])
  have hu : (U : Matrix (Fin n) (Fin n) ℂ).trace.re / n ≤ 1 :=
    (div_le_iff₀ hn0).mpr (by nlinarith [h.2])
  change 0 ≤ (1 + (U : Matrix (Fin n) (Fin n) ℂ).trace.re / n) / 2 ∧
    (1 + (U : Matrix (Fin n) (Fin n) ℂ).trace.re / n) / 2 ≤ 1
  constructor <;> linarith

@[simp] theorem specialUnitaryPeak_one (n : ℕ) (hn : 1 ≤ n) :
    specialUnitaryPeak n 1 = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp [specialUnitaryPeak, hn0]

theorem specialUnitaryPeak_eq_one_iff (n : ℕ) (hn : 1 ≤ n)
    (U : Matrix.specialUnitaryGroup (Fin n) ℂ) : specialUnitaryPeak n U = 1 ↔ U = 1 := by
  constructor
  · intro h
    apply (specialUnitary_trace_re_eq_dim_iff n U).mp
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    change (1 + (U : Matrix (Fin n) (Fin n) ℂ).trace.re / n) / 2 = 1 at h
    have hd : (U : Matrix (Fin n) (Fin n) ℂ).trace.re / n = 1 := by linarith
    exact (div_eq_one_iff_eq hn0).mp hd
  · rintro rfl
    exact specialUnitaryPeak_one n hn

/-- The product of the scalar peaks has its unique maximum at the identity of
SU(n)^K, including the empty product K=0. -/
def specialUnitaryProductPeak (n K : ℕ) : C(Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ, ℝ) where
  toFun U := ∏ i, specialUnitaryPeak n (U i)
  continuous_toFun := continuous_finset_prod _ fun i _ =>
    (specialUnitaryPeak n).continuous.comp (continuous_apply i)

theorem specialUnitaryProductPeak_nonneg (n K : ℕ) (hn : 1 ≤ n)
    (U : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ) : 0 ≤ specialUnitaryProductPeak n K U := by
  change 0 ≤ ∏ i, specialUnitaryPeak n (U i)
  exact Finset.prod_nonneg fun i _ => (specialUnitaryPeak_mem_Icc n hn (U i)).1

@[simp] theorem specialUnitaryProductPeak_one (n K : ℕ) (hn : 1 ≤ n) :
    specialUnitaryProductPeak n K 1 = 1 := by
  simp [specialUnitaryProductPeak, specialUnitaryPeak_one n hn]

theorem specialUnitaryProductPeak_unique (n K : ℕ) (hn : 1 ≤ n)
    (U : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ) (hU : U ≠ 1) :
    specialUnitaryProductPeak n K U < specialUnitaryProductPeak n K 1 := by
  classical
  rw [specialUnitaryProductPeak_one n K hn]
  have hle : specialUnitaryProductPeak n K U ≤ 1 := by
    change (∏ i, specialUnitaryPeak n (U i)) ≤ 1
    exact Finset.prod_le_one (fun i _ => (specialUnitaryPeak_mem_Icc n hn (U i)).1)
      (fun i _ => (specialUnitaryPeak_mem_Icc n hn (U i)).2)
  refine lt_of_le_of_ne hle ?_
  intro heq
  apply hU
  funext i
  apply (specialUnitaryPeak_eq_one_iff n hn (U i)).mp
  have hprod : specialUnitaryProductPeak n K U ≤ specialUnitaryPeak n (U i) := by
    change (∏ j, specialUnitaryPeak n (U j)) ≤ _
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    apply mul_le_of_le_one_right (specialUnitaryPeak_mem_Icc n hn (U i)).1
    exact Finset.prod_le_one (fun j _ => (specialUnitaryPeak_mem_Icc n hn (U j)).1)
      (fun j _ => (specialUnitaryPeak_mem_Icc n hn (U j)).2)
  have hi := (specialUnitaryPeak_mem_Icc n hn (U i)).2
  linarith

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2SpecialUnitaryApproximation -/
section
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology Matrix Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 1000000

theorem schatten_two_mul_unitary {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 2 (A * (U : Matrix (Fin n) (Fin n) ℂ)) =
      WHMultiplicativity.schattenNorm 2 A := by
  have hpos (B : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ WHMultiplicativity.schattenNorm 2 B := by
    rw [Prop5.schatten_two_eq_sqrt]
    positivity
  apply (sq_eq_sq₀ (hpos _) (hpos _)).mp
  rw [Prop5.schatten_two_sq_eq_trace, Prop5.schatten_two_sq_eq_trace]
  have hU := Matrix.mem_unitaryGroup_iff.mp U.property
  rw [Matrix.star_eq_conjTranspose] at hU
  congr 1
  rw [Matrix.conjTranspose_mul]
  have hmul : ((U : Matrix (Fin n) (Fin n) ℂ)ᴴ * Aᴴ) * (A * U) =
      (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * (Aᴴ * A) * U := by noncomm_ring
  rw [hmul, Matrix.trace_mul_cycle, ← mul_assoc, hU, one_mul]

theorem specialUnitaryProductFrobenius_right_mul {n K : ℕ}
    (U V W : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ) :
    Real.sqrt (∑ i, ∑ x, ∑ y,
      ‖((U * W) i : Matrix (Fin n) (Fin n) ℂ) x y -
        ((V * W) i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2) =
    Real.sqrt (∑ i, ∑ x, ∑ y,
      ‖(U i : Matrix (Fin n) (Fin n) ℂ) x y -
        (V i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2) := by
  have hentry (A : Matrix (Fin n) (Fin n) ℂ) :
      (∑ x, ∑ y, ‖A x y‖ ^ 2) = WHMultiplicativity.schattenNorm 2 A ^ 2 := by
    rw [Prop5.schatten_two_eq_sqrt, Real.sq_sqrt (by positivity), Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  change (∑ x, ∑ y, ‖(((U i : Matrix (Fin n) (Fin n) ℂ) * W i) -
    ((V i : Matrix (Fin n) (Fin n) ℂ) * W i)) x y‖ ^ 2) = _
  rw [hentry, ← Matrix.sub_mul]
  trans WHMultiplicativity.schattenNorm 2
    ((U i : Matrix (Fin n) (Fin n) ℂ) - (V i : Matrix (Fin n) (Fin n) ℂ)) ^ 2
  · exact congrArg (fun t : ℝ => t ^ 2)
      (schatten_two_mul_unitary _ (specialUnitaryInclusion n (W i)))
  · exact (hentry _).symm

/-- Every continuous function on SU(n)^K admits uniform normalized-power
convolution approximation, with an explicit polynomial peak kernel. -/
theorem specialUnitary_peakConvolution_tendsto (n K : ℕ) (hn : 1 ≤ n)
    (F : C(Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ, ℝ)) :
    Tendsto (fun m : ℕ => peakConvolution (Measure.pi (fun _ : Fin K => specialUnitaryHaar n))
      (specialUnitaryProductPeak n K) m F) atTop (𝓝 F) := by
  letI : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin n) ℂ) := inferInstance
  apply peakConvolution_tendsto
  · exact specialUnitaryProductPeak_nonneg n K hn
  · rw [specialUnitaryProductPeak_one n K hn]; norm_num
  · exact specialUnitaryProductPeak_unique n K hn

/-- The approximants preserve the ambient product Frobenius Lipschitz constant,
with no loss depending on n, K, or the polynomial degree. -/
theorem specialUnitary_peakConvolution_lipschitz (n K : ℕ) (hn : 1 ≤ n)
    (F : C(Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ, ℝ)) (L : ℝ)
    (hLip : ∀ U V : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ,
      |F U - F V| ≤ L * Real.sqrt (∑ i, ∑ x, ∑ y,
        ‖(U i : Matrix (Fin n) (Fin n) ℂ) x y -
          (V i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2))
    (m : ℕ) (U V : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ) :
    |peakConvolution (Measure.pi (fun _ : Fin K => specialUnitaryHaar n))
        (specialUnitaryProductPeak n K) m F U -
      peakConvolution (Measure.pi (fun _ : Fin K => specialUnitaryHaar n))
        (specialUnitaryProductPeak n K) m F V| ≤
      L * Real.sqrt (∑ i, ∑ x, ∑ y,
        ‖(U i : Matrix (Fin n) (Fin n) ℂ) x y -
          (V i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2) := by
  letI : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin n) ℂ) := inferInstance
  apply peakConvolution_abs_sub_le _ _ (specialUnitaryProductPeak_nonneg n K hn)
    (by rw [specialUnitaryProductPeak_one n K hn]; norm_num)
  intro W
  simpa only [specialUnitaryProductFrobenius_right_mul] using hLip (U * W) (V * W)

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2SkewExponential -/
section
open scoped Matrix ComplexConjugate

namespace BosonicLearn.Prop2
noncomputable section

/-- The determinant-exponential identity for a complex scalar multiple of a
Hermitian matrix follows directly from its unitary spectral decomposition. -/
theorem det_exp_complex_smul_hermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (c : ℂ) :
    (NormedSpace.exp (c • A)).det = Complex.exp (c * A.trace) := by
  let U := hA.eigenvectorUnitary
  have hu : IsUnit (U : Matrix ι ι ℂ) := ⟨Unitary.toUnits U, rfl⟩
  have hinv : (U : Matrix ι ι ℂ)⁻¹ = (U : Matrix ι ι ℂ)ᴴ := by
    apply Matrix.inv_eq_left_inv
    exact Matrix.mem_unitaryGroup_iff'.mp U.property
  have hspectral := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at hspectral
  change A = (U : Matrix ι ι ℂ) * Matrix.diagonal
    (fun i => (hA.eigenvalues i : ℂ)) * (U : Matrix ι ι ℂ)ᴴ at hspectral
  have hscaled : c • A = (U : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i => c * (hA.eigenvalues i : ℂ)) * (U : Matrix ι ι ℂ)⁻¹ := by
    rw [hinv]
    conv_lhs => rw [hspectral]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul]
    congr 2
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [Matrix.diagonal_apply, hij]
  rw [hscaled, Matrix.exp_conj _ _ hu, Matrix.det_conj hu, Matrix.exp_diagonal,
    Matrix.det_diagonal]
  simp_rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  rw [← Complex.exp_sum, hA.trace_eq_sum_eigenvalues, Finset.mul_sum]
  rfl

/-- A trace-zero skew-Hermitian generator has determinant-one exponentials. -/
theorem det_exp_real_smul_skew_traceless {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (hB : Bᴴ = -B) (htr : B.trace = 0) (t : ℝ) :
    (NormedSpace.exp (t • B)).det = 1 := by
  let H : Matrix ι ι ℂ := (-Complex.I) • B
  have hH : H.IsHermitian := by
    change Hᴴ = H
    simp [H, Matrix.conjTranspose_smul, hB]
  have htH : H.trace = 0 := by simp [H, Matrix.trace_smul, htr]
  have hrewrite : t • B = ((t:ℂ) * Complex.I) • H := by
    dsimp only [H]
    rw [smul_smul]
    have hc : ((t:ℂ) * Complex.I) * -Complex.I = (t:ℂ) := by
      calc
        _ = (t:ℂ) * (-(Complex.I * Complex.I)) := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
    rw [hc]
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
  rw [hrewrite, det_exp_complex_smul_hermitian H hH, htH, mul_zero, Complex.exp_zero]

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2HaarIntegrationByParts -/
section
open MeasureTheory Set Filter
open scoped Matrix ENNReal Topology Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 1200000

/-- On a compact probability space, a continuous parameter derivative can be passed
under the integral. A constant integral therefore has derivative zero. -/
theorem integral_derivative_eq_zero_of_constant
    {G : Type*} [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [IsFiniteMeasure μ]
    (F F' : ℝ → G → ℝ)
    (hF : Continuous (Function.uncurry F)) (hF' : Continuous (Function.uncurry F'))
    (hderiv : ∀ t U, HasDerivAt (fun s => F s U) (F' t U) t)
    (hconstant : ∀ t, ∫ U, F t U ∂μ = ∫ U, F 0 U ∂μ) :
    ∫ U, F' 0 U ∂μ = 0 := by
  have hc : IsCompact ((Icc (-1 : ℝ) 1) ×ˢ (univ : Set G)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := hc.bddAbove_image hF'.norm.continuousOn
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (x₀ := (0 : ℝ)) (s := Icc (-1) 1)
    (bound := fun _ => C)
    (Icc_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall (fun t =>
      (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable))
    ((hF.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (by simp)))
    ((hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun U t ht => hC (mem_image_of_mem
      (fun p : ℝ × G => ‖F' p.1 p.2‖)
      (show (t, U) ∈ (Icc (-1 : ℝ) 1) ×ˢ (univ : Set G) from ⟨ht, mem_univ U⟩))))
    (integrable_const C)
    (Filter.Eventually.of_forall (fun U t _ => hderiv t U))
  have heq : (fun t => ∫ U, F t U ∂μ) = fun _ => ∫ U, F 0 U ∂μ := funext hconstant
  rw [heq] at hi
  exact hi.2.unique (hasDerivAt_const 0 _)

/-- The infinitesimal generator of a continuous right-translation curve has zero
Haar integral. The derivative is assumed continuous, not uniformly bounded. -/
theorem haar_integral_right_derivative_zero
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsFiniteMeasure μ] [Measure.IsMulRightInvariant μ]
    (c : ℝ → G) (hc : Continuous c) (f Df : G → ℝ)
    (hf : Continuous f) (hDf : Continuous Df)
    (hderiv : ∀ t U, HasDerivAt (fun s => f (U * c s)) (Df (U * c t)) t) :
    ∫ U, Df U ∂μ = 0 := by
  have h := integral_derivative_eq_zero_of_constant μ
    (fun t U => f (U * c t)) (fun t U => Df (U * c t))
    (hf.comp (continuous_snd.mul (hc.comp continuous_fst)))
    (hDf.comp (continuous_snd.mul (hc.comp continuous_fst))) hderiv
    (fun t => by simp only [integral_mul_right_eq_self])
  simpa only [integral_mul_right_eq_self] using h

/-- Integration by parts for a right-invariant derivative of continuous functions
on a compact group, with continuously varying derivatives. -/
theorem haar_right_derivative_integration_by_parts
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsFiniteMeasure μ] [Measure.IsMulRightInvariant μ]
    (c : ℝ → G) (hc : Continuous c) (f g Df Dg : G → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hDf : Continuous Df) (hDg : Continuous Dg)
    (hdf : ∀ t U, HasDerivAt (fun s => f (U * c s)) (Df (U * c t)) t)
    (hdg : ∀ t U, HasDerivAt (fun s => g (U * c s)) (Dg (U * c t)) t) :
    ∫ U, f U * Dg U ∂μ = - ∫ U, g U * Df U ∂μ := by
  have hzero := haar_integral_right_derivative_zero μ c hc
    (fun U => f U * g U) (fun U => Df U * g U + f U * Dg U)
    (hf.mul hg) ((hDf.mul hg).add (hf.mul hDg))
    (fun t U => (hdf t U).mul (hdg t U))
  have h1 : Integrable (fun U => Df U * g U) μ :=
    (hDf.mul hg).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (by simp))
  have h2 : Integrable (fun U => f U * Dg U) μ :=
    (hf.mul hDg).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (by simp))
  rw [integral_add h1 h2] at hzero
  simpa only [mul_comm] using (eq_neg_of_add_eq_zero_right hzero)


/-- Normalized Haar measure is right invariant as well as left invariant. -/
theorem probabilityHaar_isMulRightInvariant
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [Measure.IsHaarMeasure μ] [IsProbabilityMeasure μ] :
    Measure.IsMulRightInvariant μ := by
  constructor
  intro g
  have hm : Measurable (fun x : G => x * g) := by fun_prop
  have : IsProbabilityMeasure (μ.map (fun x => x * g)) := Measure.isProbabilityMeasure_map hm.aemeasurable
  have hs := Measure.isMulLeftInvariant_eq_smul (μ.map (fun x => x * g)) μ
  have hmass := congrArg (fun ρ : Measure G => ρ univ) hs
  have hfactor : Measure.haarScalarFactor (μ.map (fun x => x * g)) μ = 1 := by
    simpa using hmass.symm
  simpa [hfactor] using hs

instance unitaryHaar_rightInvariant (n : ℕ) : Measure.IsMulRightInvariant (unitaryHaar n) :=
  probabilityHaar_isMulRightInvariant (unitaryHaar n)
instance specialUnitaryHaar_rightInvariant (n : ℕ) :
    Measure.IsMulRightInvariant (specialUnitaryHaar n) :=
  probabilityHaar_isMulRightInvariant (specialUnitaryHaar n)

local instance matrixNormedAlgebraRat (n : ℕ) : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

/-- Right-invariant differentiation of an ambient matrix function. -/
def rightMatrixDerivative {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → ℝ) (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  fderiv ℝ f A (A * B)

theorem continuous_rightMatrixDerivative {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → ℝ) (hf : ContDiff ℝ 1 f) :
    Continuous (rightMatrixDerivative B f) := by
  exact (hf.continuous_fderiv_apply (by norm_num)).comp
    (continuous_id.prodMk (continuous_id.mul continuous_const))

/-- The one-parameter unitary group generated by a skew-Hermitian matrix. -/
def skewHermitianUnitaryFlow {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : star B = -B) (t : ℝ) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨NormedSpace.exp (t • B), NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (by
    rw [skewAdjoint.mem_iff, star_smul, hB]
    simp)⟩

theorem continuous_skewHermitianUnitaryFlow {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : star B = -B) : Continuous (skewHermitianUnitaryFlow B hB) := by
  apply Continuous.subtype_mk
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

theorem hasDerivAt_rightMatrixDerivative {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (hB : star B = -B)
    (f : Matrix (Fin n) (Fin n) ℂ → ℝ) (hf : ContDiff ℝ 1 f)
    (t : ℝ) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    HasDerivAt (fun s => f (U * skewHermitianUnitaryFlow B hB s))
      (rightMatrixDerivative B f (U * skewHermitianUnitaryFlow B hB t)) t := by
  change HasDerivAt (fun s => f ((U : Matrix (Fin n) (Fin n) ℂ) * NormedSpace.exp (s • B)))
    (fderiv ℝ f ((U : Matrix (Fin n) (Fin n) ℂ) * NormedSpace.exp (t • B))
      (((U : Matrix (Fin n) (Fin n) ℂ) * NormedSpace.exp (t • B)) * B)) t
  have hf' := (hf.differentiable (by norm_num))
    ((U : Matrix (Fin n) (Fin n) ℂ) * NormedSpace.exp (t • B))
  have he := (hasDerivAt_exp_smul_const B t).const_mul
    (U : Matrix (Fin n) (Fin n) ℂ)
  simpa only [mul_assoc, Function.comp_def] using! hf'.hasFDerivAt.comp_hasDerivAt t he

/-- The Haar average of a right-invariant derivative on `U(n)` vanishes. -/
theorem unitaryHaar_integral_rightMatrixDerivative_zero {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (hB : star B = -B)
    (f : Matrix (Fin n) (Fin n) ℂ → ℝ) (hf : ContDiff ℝ 1 f) :
    ∫ U : Matrix.unitaryGroup (Fin n) ℂ,
      rightMatrixDerivative B f (U : Matrix (Fin n) (Fin n) ℂ) ∂unitaryHaar n = 0 := by
  exact haar_integral_right_derivative_zero (unitaryHaar n)
    (skewHermitianUnitaryFlow B hB) (continuous_skewHermitianUnitaryFlow B hB)
    (fun U => f U) (fun U => rightMatrixDerivative B f U)
    (hf.continuous.comp continuous_subtype_val)
    ((continuous_rightMatrixDerivative B f hf).comp continuous_subtype_val)
    (hasDerivAt_rightMatrixDerivative B hB f hf)

/-- Haar integration by parts for the concrete matrix derivative `Df(U)[U B]`. -/
theorem unitaryHaar_rightMatrixDerivative_integration_by_parts {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (hB : star B = -B)
    (f g : Matrix (Fin n) (Fin n) ℂ → ℝ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    (∫ U : Matrix.unitaryGroup (Fin n) ℂ,
      f U * rightMatrixDerivative B g U ∂unitaryHaar n) =
      -(∫ U : Matrix.unitaryGroup (Fin n) ℂ,
        g U * rightMatrixDerivative B f U ∂unitaryHaar n) := by
  exact haar_right_derivative_integration_by_parts (unitaryHaar n)
    (skewHermitianUnitaryFlow B hB) (continuous_skewHermitianUnitaryFlow B hB)
    (fun U => f U) (fun U => g U)
    (fun U => rightMatrixDerivative B f U) (fun U => rightMatrixDerivative B g U)
    (hf.continuous.comp continuous_subtype_val) (hg.continuous.comp continuous_subtype_val)
    ((continuous_rightMatrixDerivative B f hf).comp continuous_subtype_val)
    ((continuous_rightMatrixDerivative B g hg).comp continuous_subtype_val)
    (hasDerivAt_rightMatrixDerivative B hB f hf)
    (hasDerivAt_rightMatrixDerivative B hB g hg)


/-- The one-parameter special-unitary group generated by a trace-zero skew matrix. -/
def skewHermitianSpecialUnitaryFlow {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : star B = -B) (htr : B.trace = 0) (t : ℝ) :
    Matrix.specialUnitaryGroup (Fin n) ℂ :=
  ⟨NormedSpace.exp (t • B), (skewHermitianUnitaryFlow B hB t).property,
    det_exp_real_smul_skew_traceless B (by simpa only [Matrix.star_eq_conjTranspose] using hB) htr t⟩

theorem continuous_skewHermitianSpecialUnitaryFlow {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (hB : star B = -B) (htr : B.trace = 0) :
    Continuous (skewHermitianSpecialUnitaryFlow B hB htr) := by
  apply Continuous.subtype_mk
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

theorem hasDerivAt_rightMatrixDerivative_specialUnitary {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (hB : star B = -B) (htr : B.trace = 0)
    (f : Matrix (Fin n) (Fin n) ℂ → ℝ) (hf : ContDiff ℝ 1 f)
    (t : ℝ) (U : Matrix.specialUnitaryGroup (Fin n) ℂ) :
    HasDerivAt (fun s => f (U * skewHermitianSpecialUnitaryFlow B hB htr s))
      (rightMatrixDerivative B f (U * skewHermitianSpecialUnitaryFlow B hB htr t)) t :=
  hasDerivAt_rightMatrixDerivative B hB f hf t (specialUnitaryInclusion n U)

/-- The concrete invariant derivative integrates to zero under special-unitary Haar. -/
theorem specialUnitaryHaar_integral_rightMatrixDerivative_zero {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (hB : star B = -B) (htr : B.trace = 0)
    (f : Matrix (Fin n) (Fin n) ℂ → ℝ) (hf : ContDiff ℝ 1 f) :
    ∫ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
      rightMatrixDerivative B f (U : Matrix (Fin n) (Fin n) ℂ) ∂specialUnitaryHaar n = 0 := by
  exact haar_integral_right_derivative_zero (specialUnitaryHaar n)
    (skewHermitianSpecialUnitaryFlow B hB htr) (continuous_skewHermitianSpecialUnitaryFlow B hB htr)
    (fun U => f U) (fun U => rightMatrixDerivative B f U)
    (hf.continuous.comp continuous_subtype_val)
    ((continuous_rightMatrixDerivative B f hf).comp continuous_subtype_val)
    (hasDerivAt_rightMatrixDerivative_specialUnitary B hB htr f hf)

/-- Integration by parts on `SU(n)` for arbitrary trace-zero skew-Hermitian generators. -/
theorem specialUnitaryHaar_rightMatrixDerivative_integration_by_parts {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (hB : star B = -B) (htr : B.trace = 0)
    (f g : Matrix (Fin n) (Fin n) ℂ → ℝ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    (∫ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
      f U * rightMatrixDerivative B g U ∂specialUnitaryHaar n) =
      -(∫ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
        g U * rightMatrixDerivative B f U ∂specialUnitaryHaar n) := by
  exact haar_right_derivative_integration_by_parts (specialUnitaryHaar n)
    (skewHermitianSpecialUnitaryFlow B hB htr) (continuous_skewHermitianSpecialUnitaryFlow B hB htr)
    (fun U => f U) (fun U => g U)
    (fun U => rightMatrixDerivative B f U) (fun U => rightMatrixDerivative B g U)
    (hf.continuous.comp continuous_subtype_val) (hg.continuous.comp continuous_subtype_val)
    ((continuous_rightMatrixDerivative B f hf).comp continuous_subtype_val)
    ((continuous_rightMatrixDerivative B g hg).comp continuous_subtype_val)
    (hasDerivAt_rightMatrixDerivative_specialUnitary B hB htr f hf)
    (hasDerivAt_rightMatrixDerivative_specialUnitary B hB htr g hg)

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ProductFrameGradient -/
section
open Filter
open scoped Matrix BigOperators Topology Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 1200000

local instance productGradientMatrixNormedAlgebraRat (n : ℕ) :
    NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

/-- The direct sum of the scalar Parseval frames gives the exact Hilbert--Schmidt
dual estimate, independent of the number of factors. -/
theorem specialUnitaryProductFrame_energy_le {ι τ : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype τ] [DecidableEq τ]
    (ell : (τ → Matrix ι ι ℂ) →ₗ[ℝ] ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ B : τ → Matrix ι ι ℂ, (∀ i, (B i)ᴴ = -B i) →
      (∀ i, (B i).trace = 0) → |ell B| ≤ L * Real.sqrt (∑ i, matrixFrobeniusSq (B i))) :
    (∑ i, ∑ a : SpecialUnitaryFrameIndex ι,
      (ell (Pi.single i (specialUnitaryFrame a))) ^ 2) ≤ L ^ 2 := by
  let elli (i : τ) : Matrix ι ι ℂ →ₗ[ℝ] ℝ :=
    ell.comp (LinearMap.single ℝ (fun _ : τ => Matrix ι ι ℂ) i)
  let R : τ → Matrix ι ι ℂ := fun i => specialUnitaryFrameGradient (elli i)
  have hsk (i : τ) : (R i)ᴴ = -R i := specialUnitaryFrameGradient_skew (elli i)
  have htr (i : τ) : (R i).trace = 0 := specialUnitaryFrameGradient_trace (elli i)
  have he (i : τ) : elli i (R i) = ∑ a : SpecialUnitaryFrameIndex ι,
      (ell (Pi.single i (specialUnitaryFrame a))) ^ 2 := by
    change elli i (specialUnitaryFrameGradient (elli i)) = _
    simp only [specialUnitaryFrameGradient, map_sum, map_smul, smul_eq_mul, pow_two]
    rfl
  have heall : ell R = ∑ i, ∑ a : SpecialUnitaryFrameIndex ι,
      (ell (Pi.single i (specialUnitaryFrame a))) ^ 2 := by
    have hsum : R = ∑ i, Pi.single i (R i) := by ext i; simp
    rw [hsum, map_sum]
    exact Finset.sum_congr rfl fun i _ => he i
  have hn : (∑ i, matrixFrobeniusSq (R i)) = ∑ i, ∑ a : SpecialUnitaryFrameIndex ι,
      (ell (Pi.single i (specialUnitaryFrame a))) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    exact specialUnitaryFrameGradient_energy (elli i)
  have hb := hbound R hsk htr
  rw [heall, hn] at hb
  have he0 : 0 ≤ ∑ i, ∑ a : SpecialUnitaryFrameIndex ι,
      (ell (Pi.single i (specialUnitaryFrame a))) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => sq_nonneg _
  rw [abs_of_nonneg he0] at hb
  have hs := Real.sq_sqrt he0
  have hs0 := Real.sqrt_nonneg (∑ i, ∑ a : SpecialUnitaryFrameIndex ι,
      (ell (Pi.single i (specialUnitaryFrame a))) ^ 2)
  have hroot : Real.sqrt (∑ i, ∑ a : SpecialUnitaryFrameIndex ι,
      (ell (Pi.single i (specialUnitaryFrame a))) ^ 2) ≤ L := by
    by_contra h
    have hp := mul_pos (sub_pos.mpr (lt_of_not_ge h)) (hL.trans_lt (lt_of_not_ge h))
    nlinarith
  have hsq := pow_le_pow_left₀ hs0 hroot 2
  rwa [hs] at hsq

/-- A bound between two curves passes to their velocities. This form only needs
the Lipschitz estimate along the curve, rather than an ambient extension. -/
theorem abs_derivative_le_norm_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → ℝ) (g : ℝ → E) (df : ℝ) (dg : E)
    (hf : HasDerivAt f df 0) (hg : HasDerivAt g dg 0) (L : ℝ)
    (hLip : ∀ t, |f t - f 0| ≤ L * ‖g t - g 0‖) : |df| ≤ L * ‖dg‖ := by
  have hft := hf.tendsto_slope_zero.norm
  have hgt := hg.tendsto_slope_zero.norm.const_mul L
  apply le_of_tendsto_of_tendsto hft hgt
  apply Filter.Eventually.of_forall
  intro t
  simp only [zero_add, norm_smul, Real.norm_eq_abs]
  calc
    |t⁻¹| * |f t - f 0| ≤ |t⁻¹| * (L * ‖g t - g 0‖) :=
      mul_le_mul_of_nonneg_left (hLip t) (abs_nonneg _)
    _ = _ := by ring

/-- Flattening a tuple of complex matrices into one Euclidean space. -/
def matrixProductVector (n K : ℕ) : (Fin K → Matrix (Fin n) (Fin n) ℂ) →ₗ[ℝ]
    EuclideanSpace ℂ (Fin K × Fin n × Fin n) where
  toFun A := WithLp.toLp 2 (fun p => A p.1 p.2.1 p.2.2)
  map_add' A B := by ext p; rfl
  map_smul' r A := by ext p; rfl

theorem norm_matrixProductVector (n K : ℕ) (A : Fin K → Matrix (Fin n) (Fin n) ℂ) :
    ‖matrixProductVector n K A‖ = Real.sqrt (∑ i, matrixFrobeniusSq (A i)) := by
  rw [EuclideanSpace.norm_eq]
  change Real.sqrt (∑ p : Fin K × Fin n × Fin n, ‖A p.1 p.2.1 p.2.2‖ ^ 2) = _
  simp only [Fintype.sum_prod_type, matrixFrobeniusSq_eq_sum_norm_sq]

theorem matrixFrobeniusSq_mul_left_unitary {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    matrixFrobeniusSq ((U : Matrix (Fin n) (Fin n) ℂ) * B) = matrixFrobeniusSq B := by
  have hs (A : Matrix (Fin n) (Fin n) ℂ) :
      matrixFrobeniusSq A = WHMultiplicativity.schattenNorm 2 A ^ 2 := by
    rw [matrixFrobeniusSq_eq_sum_norm_sq, Prop5.schatten_two_eq_sqrt,
      Real.sq_sqrt (by positivity), Finset.sum_comm]
  rw [hs, hs, Prop5.schatten_two_sq_eq_trace, Prop5.schatten_two_sq_eq_trace]
  have hU := Matrix.mem_unitaryGroup_iff'.mp U.property
  rw [Matrix.star_eq_conjTranspose] at hU
  rw [Matrix.conjTranspose_mul, mul_assoc, ← mul_assoc (U : Matrix (Fin n) (Fin n) ℂ)ᴴ,
    hU, one_mul]

def specialUnitaryProductFlow {n K : ℕ} (B : Fin K → Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0) (t : ℝ) :
    Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ :=
  fun i => skewHermitianSpecialUnitaryFlow (B i) (hB i) (htr i) t

@[simp] theorem specialUnitaryProductFlow_zero {n K : ℕ}
    (B : Fin K → Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0) :
    specialUnitaryProductFlow B hB htr 0 = 1 := by
  funext i
  apply Subtype.ext
  simp [specialUnitaryProductFlow, skewHermitianSpecialUnitaryFlow]

/-- The ambient Frobenius Lipschitz bound controls the differential in every
simultaneous special-unitary tangent direction, with the product Euclidean norm. -/
theorem specialUnitaryProduct_directional_bound {n K : ℕ}
    (F : (Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ) → ℝ)
    (U : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ)
    (B : Fin K → Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0)
    (df L : ℝ)
    (hdf : HasDerivAt (fun t => F (U * specialUnitaryProductFlow B hB htr t)) df 0)
    (hLip : ∀ V W : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ,
      |F V - F W| ≤ L * Real.sqrt (∑ i, ∑ x, ∑ y,
        ‖(V i : Matrix (Fin n) (Fin n) ℂ) x y -
          (W i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2)) :
    |df| ≤ L * Real.sqrt (∑ i, matrixFrobeniusSq (B i)) := by
  let g : ℝ → EuclideanSpace ℂ (Fin K × Fin n × Fin n) := fun t =>
    matrixProductVector n K (fun i =>
      ((U * specialUnitaryProductFlow B hB htr t) i : Matrix (Fin n) (Fin n) ℂ))
  have hc : HasDerivAt
      (fun t : ℝ => fun i : Fin K => (U i : Matrix (Fin n) (Fin n) ℂ) * NormedSpace.exp (t • B i))
      (fun i => (U i : Matrix (Fin n) (Fin n) ℂ) * B i) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      (hasDerivAt_exp_smul_const (B i) (0 : ℝ)).const_mul (U i : Matrix (Fin n) (Fin n) ℂ)
  have hg : HasDerivAt g
      (matrixProductVector n K (fun i => (U i : Matrix (Fin n) (Fin n) ℂ) * B i)) 0 :=
    (matrixProductVector n K).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hc
  have hb := abs_derivative_le_norm_derivative
    (fun t => F (U * specialUnitaryProductFlow B hB htr t)) g df _ hdf hg L (by
      intro t
      dsimp only [g]
      rw [specialUnitaryProductFlow_zero, mul_one, ← map_sub, norm_matrixProductVector]
      simpa only [Pi.sub_apply, matrixFrobeniusSq_eq_sum_norm_sq, Matrix.sub_apply] using
        hLip (U * specialUnitaryProductFlow B hB htr t) U)
  rw [norm_matrixProductVector] at hb
  have hn : (∑ i, matrixFrobeniusSq ((U i : Matrix (Fin n) (Fin n) ℂ) * B i)) =
      ∑ i, matrixFrobeniusSq (B i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact matrixFrobeniusSq_mul_left_unitary (specialUnitaryInclusion n (U i)) (B i)
  rwa [hn] at hb

/-- Product-frame gradient control for a differentiable function on the group.
Only its genuine directional derivatives on SU(n)^K are required. -/
theorem specialUnitaryProduct_lipschitz_gradient_sq_le {n K : ℕ} (hn : 1 ≤ n)
    (F : (Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ) → ℝ)
    (U : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ)
    (ell : (Fin K → Matrix (Fin n) (Fin n) ℂ) →ₗ[ℝ] ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hderiv : ∀ (B : Fin K → Matrix (Fin n) (Fin n) ℂ)
      (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0),
      HasDerivAt (fun t => F (U * specialUnitaryProductFlow B hB htr t)) (ell B) 0)
    (hLip : ∀ V W : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ,
      |F V - F W| ≤ L * Real.sqrt (∑ i, ∑ x, ∑ y,
        ‖(V i : Matrix (Fin n) (Fin n) ℂ) x y -
          (W i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2)) :
    (∑ i, ∑ a : SpecialUnitaryFrameIndex (Fin n),
      (ell (Pi.single i (specialUnitaryFrame a))) ^ 2) ≤ L ^ 2 := by
  letI : NeZero n := ⟨by omega⟩
  apply specialUnitaryProductFrame_energy_le ell L hL
  intro B hB htr
  have hBs : ∀ i, star (B i) = -B i := by
    simpa only [Matrix.star_eq_conjTranspose] using hB
  exact specialUnitaryProduct_directional_bound F U B hBs htr (ell B) L
    (hderiv B hBs htr) hLip

def matrixProductRightTangent {n K : ℕ} (A : Fin K → Matrix (Fin n) (Fin n) ℂ) :
    (Fin K → Matrix (Fin n) (Fin n) ℂ) →ₗ[ℝ] (Fin K → Matrix (Fin n) (Fin n) ℂ) where
  toFun B := fun i => A i * B i
  map_add' B C := by ext i x y; simp [Matrix.mul_add]
  map_smul' r B := by ext i x y; simp [Matrix.mul_smul]

def rightMatrixProductDifferential {n K : ℕ}
    (f : (Fin K → Matrix (Fin n) (Fin n) ℂ) → ℝ)
    (A : Fin K → Matrix (Fin n) (Fin n) ℂ) :
    (Fin K → Matrix (Fin n) (Fin n) ℂ) →ₗ[ℝ] ℝ :=
  (fderiv ℝ f A).toLinearMap.comp (matrixProductRightTangent A)

theorem hasDerivAt_rightMatrixProductDifferential {n K : ℕ}
    (f : (Fin K → Matrix (Fin n) (Fin n) ℂ) → ℝ)
    (U : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ)
    (hf : DifferentiableAt ℝ f (fun i => (U i : Matrix (Fin n) (Fin n) ℂ)))
    (B : Fin K → Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0) :
    HasDerivAt (fun t => f (fun i =>
      ((U * specialUnitaryProductFlow B hB htr t) i : Matrix (Fin n) (Fin n) ℂ)))
      (rightMatrixProductDifferential f (fun i => (U i : Matrix (Fin n) (Fin n) ℂ)) B) 0 := by
  have hc : HasDerivAt
      (fun t : ℝ => fun i : Fin K => (U i : Matrix (Fin n) (Fin n) ℂ) * NormedSpace.exp (t • B i))
      (fun i => (U i : Matrix (Fin n) (Fin n) ℂ) * B i) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      (hasDerivAt_exp_smul_const (B i) (0 : ℝ)).const_mul (U i : Matrix (Fin n) (Fin n) ℂ)
  have hf' : HasFDerivAt f (fderiv ℝ f (fun i => (U i : Matrix (Fin n) (Fin n) ℂ)))
      (fun i => (U i : Matrix (Fin n) (Fin n) ℂ) * NormedSpace.exp ((0 : ℝ) • B i)) := by
    simpa only [zero_smul, NormedSpace.exp_zero, mul_one] using hf.hasFDerivAt
  exact hf'.comp_hasDerivAt 0 hc

/-- Fully concrete product-group gradient bound for an ambient differentiable
function, ready to apply to the polynomial approximation and heat spaces. -/
theorem rightMatrixProductDifferential_energy_le {n K : ℕ} (hn : 1 ≤ n)
    (f : (Fin K → Matrix (Fin n) (Fin n) ℂ) → ℝ)
    (U : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ)
    (hf : DifferentiableAt ℝ f (fun i => (U i : Matrix (Fin n) (Fin n) ℂ)))
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ V W : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ,
      |f (fun i => (V i : Matrix (Fin n) (Fin n) ℂ)) -
        f (fun i => (W i : Matrix (Fin n) (Fin n) ℂ))| ≤
      L * Real.sqrt (∑ i, ∑ x, ∑ y,
        ‖(V i : Matrix (Fin n) (Fin n) ℂ) x y -
          (W i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2)) :
    (∑ i, ∑ a : SpecialUnitaryFrameIndex (Fin n),
      (rightMatrixProductDifferential f (fun i => (U i : Matrix (Fin n) (Fin n) ℂ))
        (Pi.single i (specialUnitaryFrame a))) ^ 2) ≤ L ^ 2 := by
  apply specialUnitaryProduct_lipschitz_gradient_sq_le hn
    (fun V => f (fun i => (V i : Matrix (Fin n) (Fin n) ℂ))) U _ L hL _ hLip
  exact hasDerivAt_rightMatrixProductDifferential f U hf

theorem smoothRightMatrixProductDerivative_energy_le {n K : ℕ} (hn : 1 ≤ n)
    (f : smoothMatrixProductFunctions n K)
    (U : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ V W : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ,
      |f (fun i => (V i : Matrix (Fin n) (Fin n) ℂ)) -
        f (fun i => (W i : Matrix (Fin n) (Fin n) ℂ))| ≤
      L * Real.sqrt (∑ i, ∑ x, ∑ y,
        ‖(V i : Matrix (Fin n) (Fin n) ℂ) x y -
          (W i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2)) :
    (∑ i, ∑ a : SpecialUnitaryFrameIndex (Fin n),
      (smoothRightMatrixProductDerivative (Pi.single i (specialUnitaryFrame a)) f
        (fun i => (U i : Matrix (Fin n) (Fin n) ℂ))) ^ 2) ≤ L ^ 2 := by
  exact rightMatrixProductDifferential_energy_le hn f U
    ((smoothMatrixProductFunctions_contDiff f).differentiable (by simp) _) L hL hLip

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ProductPolynomialSpace -/
section
open scoped Matrix Matrix.Norms.L2Operator ContDiff

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 1400000

/-- A fixed finite real coordinate basis for complex matrices. -/
def matrixProductPolynomialBasis (n K : ℕ) :
    Module.Basis (Fin (Module.finrank ℝ (MatrixProduct n K))) ℝ (MatrixProduct n K) :=
  Module.finBasis ℝ _

abbrev MatrixProductPolynomialCoordinate (n K : ℕ) :=
  Fin (Module.finrank ℝ (MatrixProduct n K))

/-- Real coordinate functions, bundled in the smooth ambient algebra. -/
def smoothMatrixProductCoordinate (n K : ℕ) (i : MatrixProductPolynomialCoordinate n K) : smoothMatrixProductFunctions n K :=
  ⟨(matrixProductPolynomialBasis n K).coord i, by
    change ContDiff ℝ ∞ ((matrixProductPolynomialBasis n K).coord i : MatrixProduct n K → ℝ)
    exact ((matrixProductPolynomialBasis n K).coord i).toContinuousLinearMap.contDiff⟩

/-- Constant one together with all real-linear matrix coordinates. -/
def matrixProductPolynomialGenerator (n K : ℕ) : Option (MatrixProductPolynomialCoordinate n K) → smoothMatrixProductFunctions n K
  | none => 1
  | some i => smoothMatrixProductCoordinate n K i

/-- Real polynomials of degree at most `d`, as a concrete subspace of smooth functions. -/
def matrixProductPolynomialSpace (n K d : ℕ) : Submodule ℝ (smoothMatrixProductFunctions n K) :=
  finitePolynomialSpace (matrixProductPolynomialGenerator n K) d

instance matrixProductPolynomialSpace_finiteDimensional (n K d : ℕ) :
    FiniteDimensional ℝ (matrixProductPolynomialSpace n K d) :=
  finitePolynomialSpace_finiteDimensional _ _

theorem rightMatrixProductDerivative_coordinate {n K : ℕ}
    (B : MatrixProduct n K) (i : MatrixProductPolynomialCoordinate n K)
    (A : MatrixProduct n K) :
    rightMatrixProductDerivative B (smoothMatrixProductCoordinate n K i) A =
      (matrixProductPolynomialBasis n K).coord i (A * B) := by
  change fderiv ℝ
    (((matrixProductPolynomialBasis n K).coord i).toContinuousLinearMap : MatrixProduct n K → ℝ)
    A (A * B) = _
  have h := ((matrixProductPolynomialBasis n K).coord i).toContinuousLinearMap.hasFDerivAt (x := A)
  rw [h.fderiv]
  rfl

/-- Coordinate derivatives are explicit linear combinations of the same coordinates. -/
theorem smoothRightMatrixProductDerivative_coordinate_expansion {n K : ℕ}
    (B : MatrixProduct n K) (i : MatrixProductPolynomialCoordinate n K) :
    smoothRightMatrixProductDerivative B (smoothMatrixProductCoordinate n K i) =
      ∑ j, ((matrixProductPolynomialBasis n K).coord i (matrixProductPolynomialBasis n K j * B)) •
        smoothMatrixProductCoordinate n K j := by
  apply Subtype.ext
  funext A
  change rightMatrixProductDerivative B (smoothMatrixProductCoordinate n K i) A = _
  rw [rightMatrixProductDerivative_coordinate]
  have hA := (matrixProductPolynomialBasis n K).sum_repr A
  have heq : A * B = ∑ j, ((matrixProductPolynomialBasis n K).repr A j) • (matrixProductPolynomialBasis n K j * B) := by
    calc
      A * B = (∑ j, (matrixProductPolynomialBasis n K).repr A j • matrixProductPolynomialBasis n K j) * B :=
        congrArg (fun X => X * B) hA.symm
      _ = _ := by simp only [Finset.sum_mul, smul_mul_assoc]
  rw [heq, map_sum]
  simp only [map_smul, smul_eq_mul]
  change (∑ j, (matrixProductPolynomialBasis n K).repr A j *
    (matrixProductPolynomialBasis n K).coord i (matrixProductPolynomialBasis n K j * B)) = _
  change (∑ j, (matrixProductPolynomialBasis n K).repr A j *
    (matrixProductPolynomialBasis n K).coord i (matrixProductPolynomialBasis n K j * B)) =
      smoothMatrixProductEvaluation A (∑ j,
        ((matrixProductPolynomialBasis n K).coord i (matrixProductPolynomialBasis n K j * B)) • smoothMatrixProductCoordinate n K j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul]
  change (matrixProductPolynomialBasis n K).repr A j *
    (matrixProductPolynomialBasis n K).coord i (matrixProductPolynomialBasis n K j * B) =
      (matrixProductPolynomialBasis n K).coord i (matrixProductPolynomialBasis n K j * B) *
        (matrixProductPolynomialBasis n K).coord j A
  simp only [Module.Basis.coord_apply]
  ring

/-- The invariant differential operator preserves the linear-generator span. -/
theorem matrixProductPolynomialGenerator_derivative_mem {n K : ℕ}
    (B : MatrixProduct n K) (i : Option (MatrixProductPolynomialCoordinate n K)) :
    smoothRightMatrixProductDerivation B (matrixProductPolynomialGenerator n K i) ∈
      Submodule.span ℝ (Set.range (matrixProductPolynomialGenerator n K)) := by
  cases i with
  | none => simp [matrixProductPolynomialGenerator]
  | some i =>
    change smoothRightMatrixProductDerivative B (smoothMatrixProductCoordinate n K i) ∈ _
    rw [smoothRightMatrixProductDerivative_coordinate_expansion]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    exact Submodule.subset_span (Set.mem_range_self (some j))

/-- Every right-invariant matrix derivative preserves each finite polynomial degree. -/
theorem matrixProductPolynomialSpace_invariant {n K d : ℕ}
    (B : MatrixProduct n K) {f : smoothMatrixProductFunctions n K}
    (hf : f ∈ matrixProductPolynomialSpace n K d) :
    smoothRightMatrixProductDerivative B f ∈ matrixProductPolynomialSpace n K d :=
  finitePolynomialSpace_invariant (matrixProductPolynomialGenerator n K)
    (smoothRightMatrixProductDerivation B) (matrixProductPolynomialGenerator_derivative_mem B) d hf

/-- A concrete finite-dimensional differential operator on polynomial test functions. -/
def matrixProductPolynomialDerivative (n K d : ℕ) (B : MatrixProduct n K) :
    matrixProductPolynomialSpace n K d →ₗ[ℝ] matrixProductPolynomialSpace n K d :=
  (smoothRightMatrixProductDerivative B).restrict (fun f hf => matrixProductPolynomialSpace_invariant B hf)

/-- Restriction of ambient smooth tuple functions to SU(n)^K. -/
def smoothSpecialUnitaryProductRestriction (n K : ℕ) :
    smoothMatrixProductFunctions n K →ₗ[ℝ] C(Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ, ℝ) where
  toFun f := ⟨fun U => f (fun i => (U i : Matrix (Fin n) (Fin n) ℂ)),
    (smoothMatrixProductFunctions_contDiff f).continuous.comp
      (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i))⟩
  map_add' f g := rfl
  map_smul' r f := rfl

theorem smoothSpecialUnitaryProductRestriction_derivative_zero {n K : ℕ}
    (B : MatrixProduct n K) (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0)
    (f : smoothMatrixProductFunctions n K)
    (hf : smoothSpecialUnitaryProductRestriction n K f = 0) :
    smoothSpecialUnitaryProductRestriction n K (smoothRightMatrixProductDerivative B f) = 0 := by
  ext U
  have hzero (V : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ) :
      f (fun i => (V i : Matrix (Fin n) (Fin n) ℂ)) = 0 :=
    congrArg (fun g : C(Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ, ℝ) => g V) hf
  have hd := hasDerivAt_rightMatrixProductDifferential f U
    ((smoothMatrixProductFunctions_contDiff f).differentiable (by simp) _) B hB htr
  have heq : (fun t => f (fun i =>
      ((U * specialUnitaryProductFlow B hB htr t) i : Matrix (Fin n) (Fin n) ℂ))) =
      fun _ : ℝ => (0 : ℝ) := funext fun t => hzero _
  rw [heq] at hd
  exact hd.unique (hasDerivAt_const 0 0)

def matrixProductPolynomialRestriction (n K d : ℕ) :
    matrixProductPolynomialSpace n K d →ₗ[ℝ] C(Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ, ℝ) :=
  (smoothSpecialUnitaryProductRestriction n K).comp (matrixProductPolynomialSpace n K d).subtype

/-- Actual functions on SU(n)^K represented by real polynomials of bounded degree. -/
def specialUnitaryProductPolynomialSpace (n K d : ℕ) :
    Submodule ℝ C(Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ, ℝ) :=
  (matrixProductPolynomialRestriction n K d).range

instance specialUnitaryProductPolynomialSpace_finiteDimensional (n K d : ℕ) :
    FiniteDimensional ℝ (specialUnitaryProductPolynomialSpace n K d) :=
  Module.Finite.range (matrixProductPolynomialRestriction n K d)

theorem matrixProductPolynomialRestriction_derivative_zero {n K d : ℕ}
    (B : MatrixProduct n K) (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0)
    (f : matrixProductPolynomialSpace n K d) (hf : matrixProductPolynomialRestriction n K d f = 0) :
    matrixProductPolynomialRestriction n K d (matrixProductPolynomialDerivative n K d B f) = 0 :=
  smoothSpecialUnitaryProductRestriction_derivative_zero B hB htr f hf

def specialUnitaryProductPolynomialDerivative (n K d : ℕ)
    (B : MatrixProduct n K) (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0) :
    specialUnitaryProductPolynomialSpace n K d →ₗ[ℝ] specialUnitaryProductPolynomialSpace n K d := by
  change (matrixProductPolynomialRestriction n K d).range →ₗ[ℝ]
    (matrixProductPolynomialRestriction n K d).range
  exact rangeDescendedOperator (matrixProductPolynomialRestriction n K d)
    (matrixProductPolynomialDerivative n K d B)
    (fun f hf => matrixProductPolynomialRestriction_derivative_zero B hB htr f hf)

@[simp] theorem specialUnitaryProductPolynomialDerivative_apply_image {n K d : ℕ}
    (B : MatrixProduct n K) (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0)
    (f : matrixProductPolynomialSpace n K d) :
    (specialUnitaryProductPolynomialDerivative n K d B hB htr
      ((matrixProductPolynomialRestriction n K d).rangeRestrict f) :
        C(Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ, ℝ)) =
      matrixProductPolynomialRestriction n K d (matrixProductPolynomialDerivative n K d B f) := by
  unfold specialUnitaryProductPolynomialDerivative
  exact rangeDescendedOperator_apply_image _ _ _ _


end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ProductHaarIntegral -/
section
open MeasureTheory
open scoped Matrix BigOperators Matrix.Norms.L2Operator ContDiff

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 1000000

abbrev SpecialUnitaryProduct (n K : ℕ) := Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ

instance specialUnitaryProductBorelSpace (n K : ℕ) :
    BorelSpace (SpecialUnitaryProduct n K) := by
  letI : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin n) ℂ) :=
    @TopologicalSpace.Subtype.secondCountableTopology
      (Matrix (Fin n) (Fin n) ℂ) _ _ inferInstance
  exact inferInstanceAs (BorelSpace (Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ))

def specialUnitaryProductHaar (n K : ℕ) : Measure (SpecialUnitaryProduct n K) :=
  Measure.pi (fun _ => specialUnitaryHaar n)

instance specialUnitaryProductHaar_probability (n K : ℕ) :
    IsProbabilityMeasure (specialUnitaryProductHaar n K) := by
  dsimp [specialUnitaryProductHaar]
  infer_instance

instance specialUnitaryProductHaar_openPos (n K : ℕ) :
    (specialUnitaryProductHaar n K).IsOpenPosMeasure := by
  dsimp [specialUnitaryProductHaar]
  infer_instance

instance specialUnitaryProductHaar_rightInvariant (n K : ℕ) :
    Measure.IsMulRightInvariant (specialUnitaryProductHaar n K) := by
  dsimp [specialUnitaryProductHaar]
  infer_instance

/-- Continuous inclusion of the product group into the ambient matrix product. -/
def specialUnitaryProductVal {n K : ℕ} (U : SpecialUnitaryProduct n K) : MatrixProduct n K :=
  fun i => (U i : Matrix (Fin n) (Fin n) ℂ)

theorem continuous_specialUnitaryProductVal (n K : ℕ) :
    Continuous (@specialUnitaryProductVal n K) := by
  exact continuous_pi (fun i => continuous_subtype_val.comp (continuous_apply i))

@[simp] theorem specialUnitaryProductVal_one (n K : ℕ) :
    specialUnitaryProductVal (1 : SpecialUnitaryProduct n K) = 1 := rfl

@[simp] theorem specialUnitaryProductVal_mul {n K : ℕ} (U V : SpecialUnitaryProduct n K) :
    specialUnitaryProductVal (U * V) = specialUnitaryProductVal U * specialUnitaryProductVal V := rfl

def matrixProductSpecialUnitaryFlow {n K : ℕ} (B : MatrixProduct n K)
    (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0) (t : ℝ) :
    SpecialUnitaryProduct n K := fun i => skewHermitianSpecialUnitaryFlow (B i) (hB i) (htr i) t

theorem continuous_matrixProductSpecialUnitaryFlow {n K : ℕ} (B : MatrixProduct n K)
    (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0) :
    Continuous (matrixProductSpecialUnitaryFlow B hB htr) :=
  continuous_pi (fun i => continuous_skewHermitianSpecialUnitaryFlow (B i) (hB i) (htr i))

local instance matrixProductNormedAlgebraRat (n : ℕ) :
    NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _

theorem hasDerivAt_rightMatrixProductDerivative {n K : ℕ}
    (B : MatrixProduct n K) (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0)
    (f : MatrixProduct n K → ℝ) (hf : ContDiff ℝ 1 f)
    (t : ℝ) (U : SpecialUnitaryProduct n K) :
    HasDerivAt (fun s => f (specialUnitaryProductVal (U * matrixProductSpecialUnitaryFlow B hB htr s)))
      (rightMatrixProductDerivative B f
        (specialUnitaryProductVal (U * matrixProductSpecialUnitaryFlow B hB htr t))) t := by
  have he : HasDerivAt
      (fun s => specialUnitaryProductVal (U * matrixProductSpecialUnitaryFlow B hB htr s))
      (specialUnitaryProductVal (U * matrixProductSpecialUnitaryFlow B hB htr t) * B) t := by
    apply hasDerivAt_pi.mpr
    intro i
    change HasDerivAt (fun s => (U i : Matrix (Fin n) (Fin n) ℂ) * NormedSpace.exp (s • B i))
      (((U i : Matrix (Fin n) (Fin n) ℂ) * NormedSpace.exp (t • B i)) * B i) t
    simpa only [mul_assoc] using (hasDerivAt_exp_smul_const (B i) t).const_mul
      (U i : Matrix (Fin n) (Fin n) ℂ)
  exact ((hf.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t he

theorem continuous_rightMatrixProductDerivative {n K : ℕ} (B : MatrixProduct n K)
    (f : MatrixProduct n K → ℝ) (hf : ContDiff ℝ 1 f) :
    Continuous (rightMatrixProductDerivative B f) := by
  exact (hf.continuous_fderiv (by simp)).clm_apply (continuous_id.mul continuous_const)

theorem specialUnitaryProductHaar_integral_derivative_zero {n K : ℕ}
    (B : MatrixProduct n K) (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0)
    (f : MatrixProduct n K → ℝ) (hf : ContDiff ℝ 1 f) :
    ∫ U : SpecialUnitaryProduct n K,
      rightMatrixProductDerivative B f (specialUnitaryProductVal U) ∂specialUnitaryProductHaar n K = 0 := by
  exact haar_integral_right_derivative_zero (specialUnitaryProductHaar n K)
    (matrixProductSpecialUnitaryFlow B hB htr) (continuous_matrixProductSpecialUnitaryFlow B hB htr)
    (fun U => f (specialUnitaryProductVal U))
    (fun U => rightMatrixProductDerivative B f (specialUnitaryProductVal U))
    (hf.continuous.comp (continuous_specialUnitaryProductVal n K))
    ((continuous_rightMatrixProductDerivative B f hf).comp (continuous_specialUnitaryProductVal n K))
    (hasDerivAt_rightMatrixProductDerivative B hB htr f hf)

theorem integrable_smoothSpecialUnitaryProduct {n K : ℕ} (f : smoothMatrixProductFunctions n K) :
    Integrable (fun U : SpecialUnitaryProduct n K => f (specialUnitaryProductVal U))
      (specialUnitaryProductHaar n K) :=
  ((smoothMatrixProductFunctions_contDiff f).continuous.comp (continuous_specialUnitaryProductVal n K)).integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset isClosed_closure (by simp))

def smoothSpecialUnitaryProductIntegral (n K : ℕ) : smoothMatrixProductFunctions n K →ₗ[ℝ] ℝ where
  toFun f := ∫ U : SpecialUnitaryProduct n K, f (specialUnitaryProductVal U) ∂specialUnitaryProductHaar n K
  map_add' f g := integral_add (integrable_smoothSpecialUnitaryProduct f) (integrable_smoothSpecialUnitaryProduct g)
  map_smul' r _f := integral_const_mul r _

@[simp] theorem smoothSpecialUnitaryProductIntegral_one (n K : ℕ) :
    smoothSpecialUnitaryProductIntegral n K 1 = 1 := by
  change (∫ _ : SpecialUnitaryProduct n K, (1 : ℝ) ∂specialUnitaryProductHaar n K) = 1
  simp

theorem smoothSpecialUnitaryProductIntegral_nonneg {n K : ℕ} (f : smoothMatrixProductFunctions n K)
    (hf : ∀ U : SpecialUnitaryProduct n K, 0 ≤ f (specialUnitaryProductVal U)) :
    0 ≤ smoothSpecialUnitaryProductIntegral n K f := integral_nonneg hf

theorem smoothSpecialUnitaryProductIntegral_derivative_zero {n K : ℕ}
    (B : MatrixProduct n K) (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0)
    (f : smoothMatrixProductFunctions n K) :
    smoothSpecialUnitaryProductIntegral n K (smoothRightMatrixProductDerivative B f) = 0 :=
  specialUnitaryProductHaar_integral_derivative_zero B hB htr f
    ((smoothMatrixProductFunctions_contDiff f).of_le (by exact WithTop.coe_le_coe.mpr le_top))

theorem smoothSpecialUnitaryProductIntegral_integration_by_parts {n K : ℕ}
    (B : MatrixProduct n K) (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0)
    (f g : smoothMatrixProductFunctions n K) :
    smoothSpecialUnitaryProductIntegral n K (f * smoothRightMatrixProductDerivative B g) =
      -smoothSpecialUnitaryProductIntegral n K (g * smoothRightMatrixProductDerivative B f) := by
  have h := smoothSpecialUnitaryProductIntegral_derivative_zero B hB htr (f * g)
  rw [smoothRightMatrixProductDerivative_mul, map_add] at h
  have hc : smoothRightMatrixProductDerivative B f * g = g * smoothRightMatrixProductDerivative B f := mul_comm _ _
  rw [hc] at h
  linarith

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ProductCasimir -/
section
open scoped Matrix BigOperators Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 1000000

abbrev SpecialUnitaryProductFrameIndex (n K : ℕ) :=
  Fin K × SpecialUnitaryFrameIndex (Fin n)

def specialUnitaryProductFrame {n K : ℕ} (a : SpecialUnitaryProductFrameIndex n K) :
    MatrixProduct n K := Pi.single a.1 (specialUnitaryFrame a.2)

theorem specialUnitaryProductFrame_skew {n K : ℕ} (a : SpecialUnitaryProductFrameIndex n K) :
    star (specialUnitaryProductFrame a) = -specialUnitaryProductFrame a := by
  funext i
  by_cases hi : i = a.1
  · subst i
    simpa only [specialUnitaryProductFrame, Pi.star_apply, Pi.neg_apply, Pi.single_eq_same,
      Matrix.star_eq_conjTranspose] using specialUnitaryFrame_skew a.2
  · simp [specialUnitaryProductFrame, Pi.single_eq_of_ne hi]

theorem specialUnitaryProductFrame_trace {n K : ℕ} [NeZero n]
    (a : SpecialUnitaryProductFrameIndex n K) (i : Fin K) :
    (specialUnitaryProductFrame a i).trace = 0 := by
  by_cases hi : i = a.1
  · subst i; simp [specialUnitaryProductFrame, specialUnitaryFrame_trace]
  · simp [specialUnitaryProductFrame, Pi.single_eq_of_ne hi]

theorem specialUnitaryProductFrame_commutator {n K : ℕ}
    (a b : SpecialUnitaryProductFrameIndex n K) :
    specialUnitaryProductFrame a * specialUnitaryProductFrame b -
      specialUnitaryProductFrame b * specialUnitaryProductFrame a =
      if a.1 = b.1 then Pi.single a.1
        (specialUnitaryFrame a.2 * specialUnitaryFrame b.2 -
          specialUnitaryFrame b.2 * specialUnitaryFrame a.2) else 0 := by
  funext i
  by_cases hab : a.1 = b.1
  · by_cases hi : i = a.1
    · simp [specialUnitaryProductFrame, hab, hi]
    · have hib : i ≠ b.1 := by simpa only [← hab] using hi
      simp [specialUnitaryProductFrame, hab, Pi.single_apply, hi, hib]
  · by_cases hi : i = a.1
    · simp [specialUnitaryProductFrame, hab, hi, Pi.single_eq_of_ne hab]
    · simp [specialUnitaryProductFrame, hab, Pi.single_eq_of_ne hi]

/-- Product Lie-algebra structure constants are supported on a single factor. -/
def specialUnitaryProductStructure {n K : ℕ}
    (a b c : SpecialUnitaryProductFrameIndex n K) : ℝ :=
  if a.1 = b.1 ∧ a.1 = c.1 then specialUnitaryStructure a.2 b.2 c.2 else 0

theorem specialUnitaryProductStructure_skew {n K : ℕ}
    (a b c : SpecialUnitaryProductFrameIndex n K) :
    specialUnitaryProductStructure a b c = -specialUnitaryProductStructure a c b := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  rcases c with ⟨k, c⟩
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simpa [specialUnitaryProductStructure] using specialUnitaryStructure_skew a b c
    · simp [specialUnitaryProductStructure, hik]
  · by_cases hik : i = k
    · subst k; simp [specialUnitaryProductStructure, hij]
    · simp [specialUnitaryProductStructure, hij, hik]

theorem specialUnitaryProductFrame_bracket_expansion {n K : ℕ} [NeZero n]
    (a b : SpecialUnitaryProductFrameIndex n K) :
    specialUnitaryProductFrame a * specialUnitaryProductFrame b -
      specialUnitaryProductFrame b * specialUnitaryProductFrame a =
      ∑ c : SpecialUnitaryProductFrameIndex n K,
        specialUnitaryProductStructure a b c • specialUnitaryProductFrame c := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  rw [specialUnitaryProductFrame_commutator]
  by_cases hij : i = j
  · subst j
    have h := congrArg (LinearMap.single ℝ (fun _ : Fin K => Matrix (Fin n) (Fin n) ℂ) i)
      (specialUnitaryFrame_bracket_expansion a b)
    simp_rw [complex_ofReal_smul_matrix] at h
    simp only [map_sum, map_smul, LinearMap.single_apply] at h
    simpa [specialUnitaryProductStructure, specialUnitaryProductFrame,
      Fintype.sum_prod_type (α₁ := Fin K) (α₂ := SpecialUnitaryFrameIndex (Fin n)),
      Finset.sum_ite_irrel] using h
  · simp [hij, specialUnitaryProductStructure]

/-- The coordinate frame reconstructs every tangent tuple. -/
theorem specialUnitaryProductFrame_reconstruct {n K : ℕ} [NeZero n]
    (B : MatrixProduct n K) (hB : ∀ i, (B i)ᴴ = -B i) (htr : ∀ i, (B i).trace = 0) :
    (∑ a : SpecialUnitaryProductFrameIndex n K,
      matrixRealPair (specialUnitaryFrame a.2) (B a.1) • specialUnitaryProductFrame a) = B := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply,
    Fintype.sum_prod_type (α₁ := Fin K) (α₂ := SpecialUnitaryFrameIndex (Fin n)),
    specialUnitaryProductFrame, Pi.single_apply, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact specialUnitaryFrame_reconstruct_real (B i) (hB i) (htr i)

/-- Exact product-frame curvature energy, with no dependence on the number of factors. -/
theorem specialUnitaryProductFrame_functional_commutator_sq {n K : ℕ} [NeZero n]
    (ell : MatrixProduct n K →ₗ[ℝ] ℝ) :
    (∑ a : SpecialUnitaryProductFrameIndex n K, ∑ b : SpecialUnitaryProductFrameIndex n K,
      (ell (specialUnitaryProductFrame a * specialUnitaryProductFrame b -
        specialUnitaryProductFrame b * specialUnitaryProductFrame a))^2) =
      2 * (n:ℝ) * (∑ a : SpecialUnitaryProductFrameIndex n K,
        (ell (specialUnitaryProductFrame a))^2) := by
  simp_rw [specialUnitaryProductFrame_commutator]
  simp only [Fintype.sum_prod_type (α₁ := Fin K) (α₂ := SpecialUnitaryFrameIndex (Fin n))]
  have hinner (i : Fin K) (a : SpecialUnitaryFrameIndex (Fin n)) :
      (∑ j : Fin K, ∑ b : SpecialUnitaryFrameIndex (Fin n),
        (ell (if i = j then Pi.single i
          (specialUnitaryFrame a * specialUnitaryFrame b -
            specialUnitaryFrame b * specialUnitaryFrame a) else 0))^2) =
      ∑ b : SpecialUnitaryFrameIndex (Fin n),
        (ell (Pi.single i (specialUnitaryFrame a * specialUnitaryFrame b -
          specialUnitaryFrame b * specialUnitaryFrame a)))^2 := by
    simp only [apply_ite, map_zero, ite_pow, zero_pow (by decide : 2 ≠ 0)]
    rw [Finset.sum_comm]
    simp
  simp_rw [hinner]
  have hfactor (i : Fin K) := specialUnitaryFrame_functional_commutator_sq
    (ell.comp (LinearMap.single ℝ (fun _ : Fin K => Matrix (Fin n) (Fin n) ℂ) i))
  simp only [LinearMap.comp_apply, LinearMap.single_apply, Fintype.card_fin] at hfactor
  simp_rw [hfactor]
  rw [← Finset.mul_sum]
  rfl

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2BochnerAlgebra -/
section
namespace BosonicLearn.Prop2
noncomputable section

variable {A ι : Type*} [CommRing A] [Algebra ℝ A] [Fintype ι]

/-- Sum of squares on an algebra of smooth test functions. The algebra is
explicit: differentiating arbitrary, nonsmooth functions is not assumed. -/
def derivationLaplacian (D : ι → A →ₗ[ℝ] A) : A →ₗ[ℝ] A :=
  ∑ i, (D i).comp (D i)

/-- The carré du champ attached to a Parseval family of vector fields. -/
def derivationGamma (D : ι → A →ₗ[ℝ] A) (f g : A) : A :=
  ∑ i, (D i f) * (D i g)

theorem derivationLaplacian_apply (D : ι → A →ₗ[ℝ] A) (f : A) :
    derivationLaplacian D f = ∑ i, D i (D i f) := by
  simp [derivationLaplacian]

/-- The elementary second-order product rule. -/
theorem derivation_second_product
    (D : A →ₗ[ℝ] A) (hD : ∀ f g, D (f * g) = D f * g + f * D g)
    (f g : A) :
    D (D (f*g)) = D (D f) * g + 2 * D f * D g + f * D (D g) := by
  rw [hD, map_add, hD, hD]
  ring

/-- Algebraic Bochner identity for an invariant sum-of-squares generator. -/
theorem derivation_bochner_algebra
    (D : ι → A →ₗ[ℝ] A)
    (hD : ∀ i f g, D i (f * g) = D i f * g + f * D i g)
    (hcomm : ∀ i f, D i (derivationLaplacian D f) = derivationLaplacian D (D i f))
    (f : A) :
    derivationLaplacian D (derivationGamma D f f) =
      2 * (∑ i, ∑ j, (D j (D i f))^2) +
        2 * derivationGamma D f (derivationLaplacian D f) := by
  unfold derivationGamma
  rw [map_sum]
  simp_rw [hcomm]
  simp_rw [derivationLaplacian_apply, derivation_second_product _ (hD _)]
  have hterm (i j : ι) :
      D j (D j (D i f)) * D i f + 2 * D j (D i f) * D j (D i f) +
        D i f * D j (D j (D i f)) =
      2 * (D j (D i f))^2 + 2 * D i f * D j (D j (D i f)) := by ring
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]
  ring

/-- Evaluation of the algebraic identity at a point. -/
theorem derivation_bochner_identity
    (D : ι → A →ₗ[ℝ] A)
    (hD : ∀ i f g, D i (f * g) = D i f * g + f * D i g)
    (hcomm : ∀ i f, D i (derivationLaplacian D f) = derivationLaplacian D (D i f))
    (f : A) (ev : A →ₐ[ℝ] ℝ) :
    (ev (derivationLaplacian D (derivationGamma D f f)) -
      2 * ev (derivationGamma D f (derivationLaplacian D f))) / 2 =
        ∑ i, ∑ j, (ev (D j (D i f)))^2 := by
  rw [derivation_bochner_algebra D hD hcomm]
  simp only [map_add, map_mul, map_ofNat, map_sum, map_pow]
  ring

/-- Antisymmetric second derivatives account for at least a quarter of their
squared sum. -/
theorem sum_sq_ge_quarter_antisymmetric (B : ι → ι → ℝ) :
    (∑ i, ∑ j, (B i j - B j i)^2) / 4 ≤ ∑ i, ∑ j, (B i j)^2 := by
  have h : (∑ i, ∑ j, (B i j - B j i)^2) ≤
      ∑ i, ∑ j, (2 * (B i j)^2 + 2 * (B j i)^2) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    nlinarith [sq_nonneg (B i j + B j i)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  rw [Finset.sum_comm (f := fun i j => (B j i)^2)] at h
  linarith

/-- A commutator-frame lower bound implies the curvature inequality for the
sum-of-squares generator on its smooth test-function algebra. -/
theorem derivation_gamma_two_lower
    (D : ι → A →ₗ[ℝ] A)
    (hD : ∀ i f g, D i (f * g) = D i f * g + f * D i g)
    (hcomm : ∀ i f, D i (derivationLaplacian D f) = derivationLaplacian D (D i f))
    (κ : ℝ) (ev : A →ₐ[ℝ] ℝ)
    (hcurv : ∀ f, 4 * κ * ev (derivationGamma D f f) ≤
      ∑ i, ∑ j, (ev (D i (D j f)) - ev (D j (D i f)))^2)
    (f : A) :
    κ * ev (derivationGamma D f f) ≤
      (ev (derivationLaplacian D (derivationGamma D f f)) -
        2 * ev (derivationGamma D f (derivationLaplacian D f))) / 2 := by
  rw [derivation_bochner_identity D hD hcomm]
  have h := sum_sq_ge_quarter_antisymmetric (fun i j => ev (D i (D j f)))
  have h' := hcurv f
  rw [Finset.sum_comm (f := fun i j => (ev (D j (D i f)))^2)]
  linarith

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ProductSmoothCasimir -/
section
open scoped Matrix BigOperators Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section

@[simp] theorem smoothMatrixProductEvaluation_apply {n K : ℕ} (U : MatrixProduct n K)
    (f : smoothMatrixProductFunctions n K) : smoothMatrixProductEvaluation U f = f U := rfl

/-- The concrete family of invariant derivatives along a traceless
skew-Hermitian Parseval frame. -/
def smoothSpecialUnitaryProductDerivative (n K : ℕ) :
    SpecialUnitaryProductFrameIndex n K → Module.End ℝ (smoothMatrixProductFunctions n K) :=
  fun a => smoothRightMatrixProductDerivative (specialUnitaryProductFrame a)

theorem smoothSpecialUnitaryProductDerivative_bracket (n K : ℕ) [NeZero n]
    (a b : SpecialUnitaryProductFrameIndex n K) :
    smoothSpecialUnitaryProductDerivative n K a * smoothSpecialUnitaryProductDerivative n K b -
      smoothSpecialUnitaryProductDerivative n K b * smoothSpecialUnitaryProductDerivative n K a =
      ∑ c : SpecialUnitaryProductFrameIndex n K,
        specialUnitaryProductStructure a b c • smoothSpecialUnitaryProductDerivative n K c := by
  change (smoothRightMatrixProductDerivative (specialUnitaryProductFrame a)).comp
      (smoothRightMatrixProductDerivative (specialUnitaryProductFrame b)) -
    (smoothRightMatrixProductDerivative (specialUnitaryProductFrame b)).comp
      (smoothRightMatrixProductDerivative (specialUnitaryProductFrame a)) = _
  rw [smoothRightMatrixProductDerivative_commutator, specialUnitaryProductFrame_bracket_expansion]
  change (smoothRightMatrixProductDerivativeLinear n K)
    (∑ c, specialUnitaryProductStructure a b c • specialUnitaryProductFrame c) = _
  rw [map_sum]
  simp only [map_smul]
  rfl

/-- The genuine smooth invariant derivatives commute with their sum-of-squares
Laplacian, by Casimir centrality. -/
theorem smoothSpecialUnitaryProductDerivative_laplacian_commute (n K : ℕ) [NeZero n]
    (a : SpecialUnitaryProductFrameIndex n K) (f : smoothMatrixProductFunctions n K) :
    smoothSpecialUnitaryProductDerivative n K a
      (derivationLaplacian (smoothSpecialUnitaryProductDerivative n K) f) =
      derivationLaplacian (smoothSpecialUnitaryProductDerivative n K)
        (smoothSpecialUnitaryProductDerivative n K a f) := by
  simp only [derivationLaplacian_apply]
  apply sum_squares_apply_commute_of_structure_constants
    (smoothSpecialUnitaryProductDerivative n K) specialUnitaryProductStructure specialUnitaryProductStructure_skew
  intro k i g
  have h := congrArg (fun D : Module.End ℝ (smoothMatrixProductFunctions n K) => D g)
    (smoothSpecialUnitaryProductDerivative_bracket n K k i)
  simpa using h

/-- The real differential in the generator variable at a fixed ambient matrix. -/
def smoothMatrixProductGeneratorDifferential {n K : ℕ} (f : smoothMatrixProductFunctions n K)
    (U : MatrixProduct n K) : (MatrixProduct n K) →ₗ[ℝ] ℝ where
  toFun B := smoothRightMatrixProductDerivative B f U
  map_add' B C := by
    have h := congrArg (fun D : Module.End ℝ (smoothMatrixProductFunctions n K) => D f U)
      ((smoothRightMatrixProductDerivativeLinear n K).map_add B C)
    exact h
  map_smul' r B := by
    have h := congrArg (fun D : Module.End ℝ (smoothMatrixProductFunctions n K) => D f U)
      ((smoothRightMatrixProductDerivativeLinear n K).map_smul r B)
    exact h

/-- Exact scalar commutator energy for actual smooth matrix functions. -/
theorem smoothSpecialUnitaryProductDerivative_commutator_energy (n K : ℕ) [NeZero n]
    (f : smoothMatrixProductFunctions n K) (U : MatrixProduct n K) :
    (∑ a : SpecialUnitaryProductFrameIndex n K, ∑ b : SpecialUnitaryProductFrameIndex n K,
      ((smoothSpecialUnitaryProductDerivative n K a (smoothSpecialUnitaryProductDerivative n K b f)) U -
        (smoothSpecialUnitaryProductDerivative n K b (smoothSpecialUnitaryProductDerivative n K a f)) U)^2) =
      2 * (n:ℝ) * (∑ a : SpecialUnitaryProductFrameIndex n K,
        ((smoothSpecialUnitaryProductDerivative n K a f) U)^2) := by
  have h := specialUnitaryProductFrame_functional_commutator_sq
    (smoothMatrixProductGeneratorDifferential f U)
  have hb (a b : SpecialUnitaryProductFrameIndex n K) :
      (smoothSpecialUnitaryProductDerivative n K a (smoothSpecialUnitaryProductDerivative n K b f)) U -
        (smoothSpecialUnitaryProductDerivative n K b (smoothSpecialUnitaryProductDerivative n K a f)) U =
      smoothMatrixProductGeneratorDifferential f U
        (specialUnitaryProductFrame a * specialUnitaryProductFrame b -
          specialUnitaryProductFrame b * specialUnitaryProductFrame a) := by
    have hh := congrArg (fun D : Module.End ℝ (smoothMatrixProductFunctions n K) => D f U)
      (smoothRightMatrixProductDerivative_commutator (specialUnitaryProductFrame a) (specialUnitaryProductFrame b))
    exact hh
  simp_rw [hb]
  simpa [smoothMatrixProductGeneratorDifferential, smoothSpecialUnitaryProductDerivative] using h

/-- The pointwise Bakry--Émery curvature inequality for the actual invariant
matrix derivative algebra, with the exact coefficient `n/2`. -/
theorem smoothSpecialUnitaryProduct_gamma_two_lower (n K : ℕ) [NeZero n]
    (f : smoothMatrixProductFunctions n K) (U : MatrixProduct n K) :
    ((n:ℝ)/2) * smoothMatrixProductEvaluation U
      (derivationGamma (smoothSpecialUnitaryProductDerivative n K) f f) ≤
      (smoothMatrixProductEvaluation U
        (derivationLaplacian (smoothSpecialUnitaryProductDerivative n K)
          (derivationGamma (smoothSpecialUnitaryProductDerivative n K) f f)) -
      2 * smoothMatrixProductEvaluation U
        (derivationGamma (smoothSpecialUnitaryProductDerivative n K) f
          (derivationLaplacian (smoothSpecialUnitaryProductDerivative n K) f))) / 2 := by
  apply derivation_gamma_two_lower (smoothSpecialUnitaryProductDerivative n K)
    (fun a => smoothRightMatrixProductDerivative_mul (specialUnitaryProductFrame a))
    (smoothSpecialUnitaryProductDerivative_laplacian_commute n K) ((n:ℝ)/2) (smoothMatrixProductEvaluation U)
  intro g
  have h := smoothSpecialUnitaryProductDerivative_commutator_energy n K g U
  simp only [derivationGamma, map_sum, map_mul, smoothMatrixProductEvaluation_apply]
  simp only [← pow_two]
  rw [h]
  ring_nf
  exact le_rfl

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2SumSquares -/
section
namespace BosonicLearn.Prop2
noncomputable section

section GenericSumSquares
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

/-- A finite sum of squares of skew-adjoint operators is symmetric. -/
theorem sumSquares_isSymmetric (D : ι → E →ₗ[ℝ] E)
    (hD : ∀ i x y, inner ℝ (D i x) y = -inner ℝ x (D i y)) :
    (∑ i, (D i).comp (D i)).IsSymmetric := by
  intro x y
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hD i (D i x) y, hD i x (D i y)]
  simp

/-- The same sum of squares has a nonpositive quadratic form. -/
theorem sumSquares_quadratic_nonpos (D : ι → E →ₗ[ℝ] E)
    (hD : ∀ i x y, inner ℝ (D i x) y = -inner ℝ x (D i y)) (x : E) :
    inner ℝ ((∑ i, (D i).comp (D i)) x) x ≤ 0 := by
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, sum_inner]
  apply Finset.sum_nonpos
  intro i hi
  rw [hD i (D i x) x]
  exact neg_nonpos.mpr (real_inner_self_nonneg)
end GenericSumSquares
end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ContinuousL2Subspace -/
section
open MeasureTheory
open scoped ENNReal

namespace BosonicLearn.Prop2
noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (P : Submodule ℝ C(X, ℝ))

/-- Embed a space of continuous functions into Haar `L²`. Full support makes this injective. -/
def continuousSubspaceToL2 : P →ₗ[ℝ] Lp ℝ 2 μ :=
  (ContinuousMap.toLp 2 μ ℝ).toLinearMap.comp P.subtype

theorem continuousSubspaceToL2_injective : Function.Injective (continuousSubspaceToL2 μ P) :=
  (ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) μ).comp Subtype.val_injective

/-- The actual Hilbert realization of a continuous-function subspace. -/
def continuousL2Subspace : Submodule ℝ (Lp ℝ 2 μ) := (continuousSubspaceToL2 μ P).range

instance continuousL2Subspace_finiteDimensional [FiniteDimensional ℝ P] :
    FiniteDimensional ℝ (continuousL2Subspace μ P) :=
  Module.Finite.range (continuousSubspaceToL2 μ P)

/-- The continuous representative and its `L²` class carry exactly the same linear information. -/
def continuousL2Equiv : P ≃ₗ[ℝ] continuousL2Subspace μ P :=
  LinearEquiv.ofInjective (continuousSubspaceToL2 μ P) (continuousSubspaceToL2_injective μ P)

/-- Recover the unique continuous representative of an element of the finite Hilbert space. -/
def continuousL2Representative : continuousL2Subspace μ P →ₗ[ℝ] C(X, ℝ) :=
  P.subtype.comp (continuousL2Equiv μ P).symm.toLinearMap

@[simp] theorem continuousL2Representative_equiv (f : P) :
    continuousL2Representative μ P (continuousL2Equiv μ P f) = (f : C(X, ℝ)) := by
  simp [continuousL2Representative]

theorem continuousL2_inner (f g : continuousL2Subspace μ P) :
    inner ℝ f g = ∫ x, continuousL2Representative μ P f x * continuousL2Representative μ P g x ∂μ := by
  obtain ⟨f, rfl⟩ := (continuousL2Equiv μ P).surjective f
  obtain ⟨g, rfl⟩ := (continuousL2Equiv μ P).surjective g
  change inner ℝ (ContinuousMap.toLp 2 μ ℝ (f : C(X, ℝ)))
    (ContinuousMap.toLp 2 μ ℝ (g : C(X, ℝ))) = _
  rw [ContinuousMap.inner_toLp]
  simp only [continuousL2Representative_equiv, RCLike.conj_to_real, mul_comm]

/-- On a finite-dimensional function space, convergence in `L²` gives uniform convergence. -/
def continuousL2RepresentativeCLM [FiniteDimensional ℝ P] :
    continuousL2Subspace μ P →L[ℝ] C(X, ℝ) :=
  (continuousL2Representative μ P).toContinuousLinearMap

/-- Transfer a concrete continuous-function operator to its genuine Hilbert realization. -/
def continuousL2Operator (D : P →ₗ[ℝ] P) :
    continuousL2Subspace μ P →ₗ[ℝ] continuousL2Subspace μ P :=
  (continuousL2Equiv μ P).toLinearMap.comp (D.comp (continuousL2Equiv μ P).symm.toLinearMap)

@[simp] theorem continuousL2Operator_equiv (D : P →ₗ[ℝ] P) (f : P) :
    continuousL2Operator μ P D (continuousL2Equiv μ P f) = continuousL2Equiv μ P (D f) := by
  simp [continuousL2Operator]

@[simp] theorem continuousL2Representative_operator (D : P →ₗ[ℝ] P)
    (f : continuousL2Subspace μ P) :
    continuousL2Representative μ P (continuousL2Operator μ P D f) =
      (D ((continuousL2Equiv μ P).symm f) : C(X, ℝ)) := by
  simp [continuousL2Representative, continuousL2Operator]

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2FiniteHeat -/
section
open Filter
open scoped Topology BigOperators

namespace BosonicLearn.Prop2
noncomputable section

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A finite-dimensional heat evolution in an orthonormal eigenbasis. This is an
explicit finite sum, and will satisfy the heat ODE whenever the basis diagonalizes
the specified generator. -/
def finiteSpectralHeat (b : OrthonormalBasis ι ℝ E) (lambda : ι → ℝ) (t : ℝ) : E →ₗ[ℝ] E where
  toFun v := ∑ i, (Real.exp (t * lambda i) * b.repr v i) • b i
  map_add' v w := by
    simp [map_add, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [map_smul, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring

@[simp] theorem finiteSpectralHeat_apply (b : OrthonormalBasis ι ℝ E) (lambda : ι → ℝ)
    (t : ℝ) (v : E) :
    finiteSpectralHeat b lambda t v = ∑ i, (Real.exp (t * lambda i) * b.repr v i) • b i := rfl

@[simp] theorem finiteSpectralHeat_zero (b : OrthonormalBasis ι ℝ E) (lambda : ι → ℝ) (v : E) :
    finiteSpectralHeat b lambda 0 v = v := by
  simp only [finiteSpectralHeat_apply, zero_mul, Real.exp_zero, one_mul]
  exact b.sum_repr v

@[simp] theorem finiteSpectralHeat_repr (b : OrthonormalBasis ι ℝ E) (lambda : ι → ℝ)
    (t : ℝ) (v : E) (i : ι) :
    b.repr (finiteSpectralHeat b lambda t v) i = Real.exp (t * lambda i) * b.repr v i := by
  simp [finiteSpectralHeat, map_sum, map_smul, b.repr_self, Pi.single_apply, mul_ite]

theorem finiteSpectralHeat_add (b : OrthonormalBasis ι ℝ E) (lambda : ι → ℝ)
    (s t : ℝ) (v : E) :
    finiteSpectralHeat b lambda (s+t) v = finiteSpectralHeat b lambda s (finiteSpectralHeat b lambda t v) := by
  conv_rhs => rw [finiteSpectralHeat_apply]
  simp only [finiteSpectralHeat_repr]
  rw [finiteSpectralHeat_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [add_mul, Real.exp_add]
  congr 1
  ring

/-- Projection onto the span of the zero-eigenvalue basis vectors. -/
def finiteSpectralKernelProjection (b : OrthonormalBasis ι ℝ E) (lambda : ι → ℝ) (v : E) : E :=
  ∑ i, if lambda i = 0 then b.repr v i • b i else 0

@[simp] theorem finiteSpectralKernelProjection_repr (b : OrthonormalBasis ι ℝ E)
    (lambda : ι → ℝ) (v : E) (i : ι) :
    b.repr (finiteSpectralKernelProjection b lambda v) i = if lambda i = 0 then b.repr v i else 0 := by
  have hterm (j : ι) : b.repr (if lambda j = 0 then b.repr v j • b j else 0) i =
      if j = i then (if lambda i = 0 then b.repr v i else 0) else 0 := by
    by_cases hj : lambda j = 0 <;> by_cases hji : j = i
    · subst j; simp [hj, b.repr_self]
    · simp [hj, hji, b.repr_self, Pi.single_apply, Ne.symm hji]
    · subst j; simp [hj]
    · simp [hj, hji]
  simp only [finiteSpectralKernelProjection, map_sum]
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  simp_rw [hterm]
  simp

/-- An explicit finite-dimensional spectral heat flow solves the actual linear ODE. -/
theorem finiteSpectralHeat_hasDerivAt (b : OrthonormalBasis ι ℝ E) (lambda : ι → ℝ)
    (L : E →ₗ[ℝ] E) (hdiag : ∀ i, L (b i) = lambda i • b i) (v : E) (t : ℝ) :
    HasDerivAt (fun s => finiteSpectralHeat b lambda s v)
      (L (finiteSpectralHeat b lambda t v)) t := by
  have hd (i : ι) : HasDerivAt
      (fun s => (Real.exp (s * lambda i) * b.repr v i) • b i)
      ((Real.exp (t * lambda i) * lambda i * b.repr v i) • b i) t := by
    simpa using ((((hasDerivAt_id t).mul_const (lambda i)).exp).mul_const (b.repr v i)).smul_const (b i)
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i)
  change HasDerivAt (fun s => ∑ i, (Real.exp (s * lambda i) * b.repr v i) • b i)
    (L (finiteSpectralHeat b lambda t v)) t
  convert h using 1
  rw [finiteSpectralHeat_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, hdiag, smul_smul]
  congr 1
  ring

/-- Nonpositive eigenvalues imply convergence to the kernel projection. -/
theorem finiteSpectralHeat_tendsto (b : OrthonormalBasis ι ℝ E) (lambda : ι → ℝ)
    (hlambda : ∀ i, lambda i ≤ 0) (v : E) :
    Tendsto (fun t => finiteSpectralHeat b lambda t v) atTop
      (𝓝 (finiteSpectralKernelProjection b lambda v)) := by
  apply tendsto_finset_sum
  intro i _
  by_cases hi : lambda i = 0
  · simp [hi]
  · have hneg : lambda i < 0 := lt_of_le_of_ne (hlambda i) hi
    have hlim : Tendsto (fun t : ℝ => Real.exp (t * lambda i)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (Tendsto.atTop_mul_const_of_neg hneg tendsto_id)
    simpa [hi] using (hlim.mul_const (b.repr v i)).smul_const (b i)


/-- The spectral limit belongs to the actual kernel of the generator. -/
theorem finiteSpectralKernelProjection_mem_ker (b : OrthonormalBasis ι ℝ E)
    (lambda : ι → ℝ) (L : E →ₗ[ℝ] E) (hdiag : ∀ i, L (b i) = lambda i • b i) (v : E) :
    L (finiteSpectralKernelProjection b lambda v) = 0 := by
  simp only [finiteSpectralKernelProjection, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : lambda i = 0
  · simp [hi, map_smul, hdiag]
  · simp [hi]

section SelfAdjoint
variable [FiniteDimensional ℝ E]

/-- The finite heat evolution attached to a self-adjoint real linear operator. -/
def finiteSelfAdjointHeat (L : E →ₗ[ℝ] E) (hL : L.IsSymmetric) (t : ℝ) : E →ₗ[ℝ] E :=
  finiteSpectralHeat (hL.eigenvectorBasis rfl) (hL.eigenvalues rfl) t

theorem eigenvalues_nonpos_of_quadratic_nonpos (L : E →ₗ[ℝ] E) (hL : L.IsSymmetric)
    (hneg : ∀ v : E, inner ℝ (L v) v ≤ 0) (i : Fin (Module.finrank ℝ E)) :
    hL.eigenvalues rfl i ≤ 0 := by
  have h := hneg (hL.eigenvectorBasis rfl i)
  rw [hL.apply_eigenvectorBasis rfl i, real_inner_smul_left] at h
  have hb : inner ℝ (hL.eigenvectorBasis rfl i) (hL.eigenvectorBasis rfl i) = 1 := by
    simp
  rwa [hb, mul_one] at h

@[simp] theorem finiteSelfAdjointHeat_zero (L : E →ₗ[ℝ] E) (hL : L.IsSymmetric) (v : E) :
    finiteSelfAdjointHeat L hL 0 v = v := finiteSpectralHeat_zero _ _ _

theorem finiteSelfAdjointHeat_hasDerivAt (L : E →ₗ[ℝ] E) (hL : L.IsSymmetric) (v : E) (t : ℝ) :
    HasDerivAt (fun s => finiteSelfAdjointHeat L hL s v)
      (L (finiteSelfAdjointHeat L hL t v)) t :=
  finiteSpectralHeat_hasDerivAt _ _ L (hL.apply_eigenvectorBasis rfl) v t

/-- A self-adjoint nonpositive finite-dimensional heat evolution converges to
an explicitly constructed vector in the generator kernel. -/
theorem finiteSelfAdjointHeat_tendsto_kernel (L : E →ₗ[ℝ] E) (hL : L.IsSymmetric)
    (hneg : ∀ v : E, inner ℝ (L v) v ≤ 0) (v : E) :
    ∃ q : E, L q = 0 ∧ Tendsto (fun t => finiteSelfAdjointHeat L hL t v) atTop (𝓝 q) := by
  refine ⟨finiteSpectralKernelProjection (hL.eigenvectorBasis rfl) (hL.eigenvalues rfl) v, ?_, ?_⟩
  · exact finiteSpectralKernelProjection_mem_ker _ _ L (hL.apply_eigenvectorBasis rfl) v
  · exact finiteSpectralHeat_tendsto _ _ (eigenvalues_nonpos_of_quadratic_nonpos L hL hneg) v

/-- The spectral heat limit is the orthogonal projection onto the generator kernel. -/
theorem finiteSelfAdjointHeat_tendsto_starProjection (L : E →ₗ[ℝ] E)
    (hL : L.IsSymmetric) (hneg : ∀ v : E, inner ℝ (L v) v ≤ 0) (v : E) :
    Tendsto (fun t => finiteSelfAdjointHeat L hL t v) atTop
      (𝓝 (L.ker.starProjection v)) := by
  let b := hL.eigenvectorBasis rfl
  let lambda := hL.eigenvalues rfl
  let q := finiteSpectralKernelProjection b lambda v
  have hq : L q = 0 :=
    finiteSpectralKernelProjection_mem_ker b lambda L (hL.apply_eigenvectorBasis rfl) v
  have horth (w : E) (hw : w ∈ L.ker) : inner ℝ (v - q) w = 0 := by
    rw [← b.sum_inner_mul_inner]
    apply Finset.sum_eq_zero
    intro i _
    have hwi : lambda i * b.repr w i = 0 := by
      change hL.eigenvalues rfl i * (hL.eigenvectorBasis rfl).repr w i = 0
      simpa [LinearMap.mem_ker.mp hw] using
        (hL.eigenvectorBasis_apply_self_apply rfl w i).symm
    rw [← real_inner_comm (v - q) (b i), ← b.repr_apply_apply,
      ← b.repr_apply_apply]
    change (b.repr (v - q) i) * b.repr w i = 0
    rw [map_sub, PiLp.sub_apply]
    dsimp only [q]
    rw [finiteSpectralKernelProjection_repr]
    by_cases hi : lambda i = 0
    · simp [hi]
    · simp [hi, (mul_eq_zero.mp hwi).resolve_left hi]
  have heq : L.ker.starProjection v = q :=
    L.ker.eq_starProjection_of_mem_of_inner_eq_zero hq horth
  rw [heq]
  exact finiteSpectralHeat_tendsto b lambda
    (eigenvalues_nonpos_of_quadratic_nonpos L hL hneg) v

/-- If the kernel is the constants, the heat evolution converges to its mean
coefficient along the normalized constant vector. -/
theorem finiteSelfAdjointHeat_tendsto_constant (L : E →ₗ[ℝ] E)
    (hL : L.IsSymmetric) (hneg : ∀ v : E, inner ℝ (L v) v ≤ 0)
    (one : E) (hone : inner ℝ one one = 1) (hLone : L one = 0)
    (hker : ∀ q : E, L q = 0 → ∃ c : ℝ, q = c • one) (v : E) :
    Tendsto (fun t => finiteSelfAdjointHeat L hL t v) atTop
      (𝓝 ((inner ℝ one v) • one)) := by
  have hp : L (L.ker.starProjection v) = 0 := L.ker.starProjection_apply_mem v
  obtain ⟨c, hc⟩ := hker (L.ker.starProjection v) hp
  have horth := L.ker.starProjection_inner_eq_zero v one hLone
  rw [hc, inner_sub_left, real_inner_smul_left, hone, mul_one] at horth
  have heqc : c = inner ℝ one v := by rw [real_inner_comm] at horth; linarith
  have heq : L.ker.starProjection v = (inner ℝ one v) • one := by simpa [heqc] using hc
  rw [← heq]
  exact finiteSelfAdjointHeat_tendsto_starProjection L hL hneg v

/-- Heat preserves the pairing with every stationary vector, in particular its mean. -/
theorem finiteSelfAdjointHeat_inner_kernel (L : E →ₗ[ℝ] E) (hL : L.IsSymmetric)
    (w : E) (hw : L w = 0) (v : E) (t : ℝ) :
    inner ℝ w (finiteSelfAdjointHeat L hL t v) = inner ℝ w v := by
  have hd (s : ℝ) : HasDerivAt (fun r => inner ℝ w (finiteSelfAdjointHeat L hL r v)) 0 s := by
    have h := (innerSL ℝ w).hasFDerivAt.comp_hasDerivAt s
      (finiteSelfAdjointHeat_hasDerivAt L hL v s)
    have hz : inner ℝ w (L (finiteSelfAdjointHeat L hL s v)) = 0 := by
      rw [← hL w _, hw, inner_zero_left]
    change HasDerivAt (fun r => inner ℝ w (finiteSelfAdjointHeat L hL r v))
      (inner ℝ w (L (finiteSelfAdjointHeat L hL s v))) s at h
    rwa [hz] at h
  have h := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simpa using h

end SelfAdjoint

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ProductPolynomialHilbert -/
section
open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 600000

/-- Integration by parts survives removal of the ambient vanishing ideal. -/
theorem specialUnitaryProductPolynomialDerivative_ibp {n K d : ℕ}
    (B : MatrixProduct n K) (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0)
    (f g : specialUnitaryProductPolynomialSpace n K d) :
    (∫ U, (specialUnitaryProductPolynomialDerivative n K d B hB htr f : C(_, ℝ)) U *
      (g : C(_, ℝ)) U ∂specialUnitaryProductHaar n K) =
    -(∫ U, (f : C(_, ℝ)) U *
      (specialUnitaryProductPolynomialDerivative n K d B hB htr g : C(_, ℝ)) U ∂specialUnitaryProductHaar n K) := by
  obtain ⟨p, hp⟩ := f.property
  obtain ⟨q, hq⟩ := g.property
  have hfp : f = (matrixProductPolynomialRestriction n K d).rangeRestrict p := Subtype.ext hp.symm
  have hgq : g = (matrixProductPolynomialRestriction n K d).rangeRestrict q := Subtype.ext hq.symm
  subst f; subst g
  rw [specialUnitaryProductPolynomialDerivative_apply_image, specialUnitaryProductPolynomialDerivative_apply_image]
  change (∫ U : SpecialUnitaryProduct n K,
    rightMatrixProductDerivative B (p : smoothMatrixProductFunctions n K) (specialUnitaryProductVal U) * (q : smoothMatrixProductFunctions n K) (specialUnitaryProductVal U) ∂specialUnitaryProductHaar n K) =
    -(∫ U : SpecialUnitaryProduct n K,
      (p : smoothMatrixProductFunctions n K) (specialUnitaryProductVal U) * rightMatrixProductDerivative B (q : smoothMatrixProductFunctions n K) (specialUnitaryProductVal U) ∂specialUnitaryProductHaar n K)
  have h := smoothSpecialUnitaryProductIntegral_integration_by_parts B hB htr
    (q : smoothMatrixProductFunctions n K) (p : smoothMatrixProductFunctions n K)
  change (∫ U : SpecialUnitaryProduct n K,
    (q : smoothMatrixProductFunctions n K) (specialUnitaryProductVal U) *
      rightMatrixProductDerivative B (p : smoothMatrixProductFunctions n K) (specialUnitaryProductVal U)
      ∂specialUnitaryProductHaar n K) =
    -(∫ U : SpecialUnitaryProduct n K,
      (p : smoothMatrixProductFunctions n K) (specialUnitaryProductVal U) *
        rightMatrixProductDerivative B (q : smoothMatrixProductFunctions n K) (specialUnitaryProductVal U)
        ∂specialUnitaryProductHaar n K) at h
  simpa only [mul_comm] using h



/-- Genuine finite-dimensional polynomial Hilbert space on `SU(n)`. -/
abbrev specialUnitaryProductPolynomialHilbert (n K d : ℕ) :=
  continuousL2Subspace (specialUnitaryProductHaar n K) (specialUnitaryProductPolynomialSpace n K d)

/-- Invariant differentiation on polynomial `L²` classes. -/
def specialUnitaryProductPolynomialHilbertDerivative (n K d : ℕ)
    (B : MatrixProduct n K) (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0) :
    specialUnitaryProductPolynomialHilbert n K d →ₗ[ℝ] specialUnitaryProductPolynomialHilbert n K d :=
  continuousL2Operator (specialUnitaryProductHaar n K) (specialUnitaryProductPolynomialSpace n K d)
    (specialUnitaryProductPolynomialDerivative n K d B hB htr)

theorem specialUnitaryProductPolynomialHilbertDerivative_skew {n K d : ℕ}
    (B : MatrixProduct n K) (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0)
    (f g : specialUnitaryProductPolynomialHilbert n K d) :
    inner ℝ (specialUnitaryProductPolynomialHilbertDerivative n K d B hB htr f) g =
      -inner ℝ f (specialUnitaryProductPolynomialHilbertDerivative n K d B hB htr g) := by
  let e := continuousL2Equiv (specialUnitaryProductHaar n K) (specialUnitaryProductPolynomialSpace n K d)
  obtain ⟨f, rfl⟩ := e.surjective f
  obtain ⟨g, rfl⟩ := e.surjective g
  change inner ℝ (continuousL2Operator _ _ _ (e f)) (e g) =
    -inner ℝ (e f) (continuousL2Operator _ _ _ (e g))
  rw [continuousL2Operator_equiv, continuousL2Operator_equiv,
    continuousL2_inner, continuousL2_inner]
  simp only [e, continuousL2Representative_equiv]
  exact specialUnitaryProductPolynomialDerivative_ibp B hB htr f g



/-- The concrete finite-dimensional SU Laplacian, with all ambient relations removed. -/
def specialUnitaryProductPolynomialHilbertLaplacian (n K d : ℕ) [NeZero n] :
    specialUnitaryProductPolynomialHilbert n K d →ₗ[ℝ] specialUnitaryProductPolynomialHilbert n K d :=
  ∑ a : SpecialUnitaryProductFrameIndex n K,
    let D := specialUnitaryProductPolynomialHilbertDerivative n K d (specialUnitaryProductFrame a)
      (fun i => congrFun (specialUnitaryProductFrame_skew a) i) (specialUnitaryProductFrame_trace a)
    D.comp D

theorem specialUnitaryProductPolynomialHilbertLaplacian_symmetric (n K d : ℕ) [NeZero n] :
    (specialUnitaryProductPolynomialHilbertLaplacian n K d).IsSymmetric := by
  apply sumSquares_isSymmetric
  intro a f g
  exact specialUnitaryProductPolynomialHilbertDerivative_skew _ _ _ f g

theorem specialUnitaryProductPolynomialHilbertLaplacian_nonpos (n K d : ℕ) [NeZero n]
    (f : specialUnitaryProductPolynomialHilbert n K d) :
    inner ℝ (specialUnitaryProductPolynomialHilbertLaplacian n K d f) f ≤ 0 := by
  apply sumSquares_quadratic_nonpos
  intro a x y
  exact specialUnitaryProductPolynomialHilbertDerivative_skew _ _ _ x y

/-- An actual finite-dimensional heat evolution on polynomial SU functions. -/
def specialUnitaryProductPolynomialHeat (n K d : ℕ) [NeZero n] (t : ℝ) :
    specialUnitaryProductPolynomialHilbert n K d →ₗ[ℝ] specialUnitaryProductPolynomialHilbert n K d :=
  finiteSelfAdjointHeat (specialUnitaryProductPolynomialHilbertLaplacian n K d)
    (specialUnitaryProductPolynomialHilbertLaplacian_symmetric n K d) t

theorem specialUnitaryProductPolynomialHeat_hasDerivAt (n K d : ℕ) [NeZero n]
    (f : specialUnitaryProductPolynomialHilbert n K d) (t : ℝ) :
    HasDerivAt (fun s => specialUnitaryProductPolynomialHeat n K d s f)
      (specialUnitaryProductPolynomialHilbertLaplacian n K d (specialUnitaryProductPolynomialHeat n K d t f)) t :=
  finiteSelfAdjointHeat_hasDerivAt _ _ f t

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2SpecialUnitaryLogarithm -/
section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator
open Complex

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 1000000

/-- On a finite matrix spectrum, the argument is continuous even when the
spectrum contains the branch-cut point. Thus every unitary matrix has a
self-adjoint logarithm, without a small-norm assumption. -/
theorem matrix_expUnitary_argSelfAdjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : Matrix.unitaryGroup ι ℂ) :
    selfAdjoint.expUnitary (Unitary.argSelfAdjoint u) = u := by
  apply Subtype.ext
  have : ContinuousOn arg (spectrum ℂ (u : Matrix ι ι ℂ)) :=
    (Matrix.finite_spectrum _).continuousOn _
  rw [selfAdjoint.expUnitary_coe, Unitary.argSelfAdjoint_coe,
    ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← cfc_comp_smul .., ← cfc_comp' ..]
  conv_rhs => rw [← cfc_id' ℂ (u : Matrix ι ι ℂ)]
  refine cfc_congr fun y hy ↦ ?_
  have hy₁ : ‖y‖ = 1 := spectrum.norm_eq_one_of_unitary u.2 hy
  have : I * y.arg = log y :=
    Complex.ext (by simp [log_re, hy₁]) (by simp [log_im])
  simpa [← exp_eq_exp_ℂ, this] using exp_log (by aesop)

/-- A determinant-one Hermitian exponential can be represented by a trace-zero
skew-Hermitian generator. One eigenangle is changed by the total eigenangle;
the determinant condition makes that change invisible after exponentiation. -/
theorem exists_traceless_skew_exp_of_hermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (hdet : (NormedSpace.exp (I • H)).det = 1) :
    ∃ B : Matrix ι ι ℂ, Bᴴ = -B ∧ B.trace = 0 ∧
      NormedSpace.exp B = NormedSpace.exp (I • H) := by
  let V := hH.eigenvectorUnitary
  let theta := hH.eigenvalues
  let j : ι := Classical.choice inferInstance
  let total : ℝ := ∑ i, theta i
  let phi : ι → ℝ := fun i => theta i - if i = j then total else 0
  have hsum : ∑ i, phi i = 0 := by simp [phi, total, Finset.sum_sub_distrib]
  have hperiod : Complex.exp (I * (total : ℂ)) = 1 := by
    rw [det_exp_complex_smul_hermitian H hH] at hdet
    simpa [total, theta, hH.trace_eq_sum_eigenvalues] using hdet
  have hexpphi (i : ι) : Complex.exp (I * (phi i : ℂ)) =
      Complex.exp (I * (theta i : ℂ)) := by
    by_cases hi : i = j
    · simp only [phi, hi, ite_true, ofReal_sub, mul_sub, Complex.exp_sub, hperiod, div_one]
    · simp [phi, hi]
  have hunit : IsUnit (V : Matrix ι ι ℂ) := ⟨Unitary.toUnits V, rfl⟩
  have hinv : (V : Matrix ι ι ℂ)⁻¹ = (V : Matrix ι ι ℂ)ᴴ :=
    Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp V.property)
  have hspectral : H = (V : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i => (theta i : ℂ)) * (V : Matrix ι ι ℂ)ᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at h
    exact h
  let A : Matrix ι ι ℂ := (V : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i => (phi i : ℂ)) * (V : Matrix ι ι ℂ)ᴴ
  have hA : A.IsHermitian := by
    change Aᴴ = A
    have hd : (Matrix.diagonal (fun i => (phi i : ℂ))).IsHermitian :=
      Matrix.isHermitian_diagonal_iff.mpr (fun i => by simp [isSelfAdjoint_iff])
    simp only [A, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hd.eq,
      Matrix.mul_assoc]
  have htrace : A.trace = 0 := by
    dsimp only [A]
    have hv : (V : Matrix ι ι ℂ)ᴴ * (V : Matrix ι ι ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp V.property
    rw [Matrix.trace_mul_cycle, hv, Matrix.one_mul, Matrix.trace_diagonal]
    exact_mod_cast hsum
  have hexpconj (a : ι → ℝ) :
      NormedSpace.exp (I • ((V : Matrix ι ι ℂ) *
        Matrix.diagonal (fun i => (a i : ℂ)) * (V : Matrix ι ι ℂ)ᴴ)) =
      (V : Matrix ι ι ℂ) * Matrix.diagonal (fun i => Complex.exp (I * (a i : ℂ))) *
        (V : Matrix ι ι ℂ)ᴴ := by
    have hscale : I • ((V : Matrix ι ι ℂ) *
        Matrix.diagonal (fun i => (a i : ℂ)) * (V : Matrix ι ι ℂ)ᴴ) =
        (V : Matrix ι ι ℂ) * Matrix.diagonal (fun i => I * (a i : ℂ)) *
          (V : Matrix ι ι ℂ)⁻¹ := by
      rw [hinv, ← Matrix.smul_mul, ← Matrix.mul_smul]
      congr 2
      ext i k
      by_cases hik : i = k
      · subst k; simp
      · simp [Matrix.diagonal_apply, hik]
    rw [hscale, Matrix.exp_conj _ _ hunit, Matrix.exp_diagonal, hinv]
    simp only [Pi.exp_def, Complex.exp_eq_exp_ℂ]
  refine ⟨I • A, ?_, ?_, ?_⟩
  · simp [Matrix.conjTranspose_smul, hA.eq]
  · simp [Matrix.trace_smul, htrace]
  · change NormedSpace.exp (I • A) = _
    dsimp only [A]
    rw [hexpconj]
    conv_rhs => rw [hspectral, hexpconj]
    simp_rw [hexpphi]

/-- Every special-unitary matrix is the exponential of a trace-zero
skew-Hermitian matrix. -/
theorem specialUnitary_exists_skew_traceless_log {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (U : Matrix.specialUnitaryGroup ι ℂ) :
    ∃ B : Matrix ι ι ℂ, Bᴴ = -B ∧ B.trace = 0 ∧
      NormedSpace.exp B = (U : Matrix ι ι ℂ) := by
  let u : Matrix.unitaryGroup ι ℂ := ⟨U, U.property.1⟩
  let H : selfAdjoint (Matrix ι ι ℂ) := Unitary.argSelfAdjoint u
  have he : NormedSpace.exp (I • (H : Matrix ι ι ℂ)) = (U : Matrix ι ι ℂ) :=
    congrArg Subtype.val (matrix_expUnitary_argSelfAdjoint u)
  have hh : (H : Matrix ι ι ℂ).IsHermitian := H.property
  obtain ⟨B, hB, ht, heB⟩ := exists_traceless_skew_exp_of_hermitian
    (H : Matrix ι ι ℂ) hh (by rw [he]; exact U.property.2)
  exact ⟨B, hB, ht, heB.trans he⟩

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ProductKernel -/
section
open MeasureTheory
open scoped Matrix BigOperators Matrix.Norms.L2Operator ContDiff

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 1000000

/-- A function whose invariant derivatives vanish is constant on a finite
product of special-unitary groups. All factors move along their logarithms at once. -/
theorem specialUnitaryProduct_const_of_right_derivative_zero {n K : ℕ} [NeZero n]
    (f : MatrixProduct n K → ℝ) (hf : ContDiff ℝ 1 f)
    (hzero : ∀ (B : MatrixProduct n K), (∀ i, (B i)ᴴ = -B i) →
      (∀ i, (B i).trace = 0) → ∀ U : SpecialUnitaryProduct n K,
        rightMatrixProductDerivative B f (specialUnitaryProductVal U) = 0)
    (U : SpecialUnitaryProduct n K) : f (specialUnitaryProductVal U) = f 1 := by
  choose B hB htr hU using fun i => specialUnitary_exists_skew_traceless_log (U i)
  have hs : ∀ i, star (B i) = -B i := hB
  let gamma := matrixProductSpecialUnitaryFlow B hs htr
  have hd (t : ℝ) : HasDerivAt (fun s => f (specialUnitaryProductVal (gamma s))) 0 t := by
    have hh := hasDerivAt_rightMatrixProductDerivative B hs htr f hf t 1
    simp only [one_mul] at hh
    rw [hzero B hB htr (gamma t)] at hh
    exact hh
  have heq := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) (1 : ℝ) 0
  have h1 : specialUnitaryProductVal (gamma 1) = specialUnitaryProductVal U := by
    funext i
    simpa [gamma, matrixProductSpecialUnitaryFlow, specialUnitaryProductVal,
      skewHermitianSpecialUnitaryFlow] using hU i
  have h0 : specialUnitaryProductVal (gamma 0) = 1 := by
    funext i
    simp [gamma, matrixProductSpecialUnitaryFlow, specialUnitaryProductVal,
      skewHermitianSpecialUnitaryFlow]
  simpa only [h1, h0] using heq

theorem specialUnitaryProduct_const_of_frame_derivative_zero {n K : ℕ} [NeZero n]
    (f : smoothMatrixProductFunctions n K)
    (hzero : ∀ a : SpecialUnitaryProductFrameIndex n K,
      ∀ U : SpecialUnitaryProduct n K,
        smoothSpecialUnitaryProductDerivative n K a f (specialUnitaryProductVal U) = 0)
    (U : SpecialUnitaryProduct n K) : f (specialUnitaryProductVal U) = f 1 := by
  apply specialUnitaryProduct_const_of_right_derivative_zero f
    ((smoothMatrixProductFunctions_contDiff f).of_le (by simp)) _ U
  intro B hB htr V
  have h := congrArg (smoothMatrixProductGeneratorDifferential f (specialUnitaryProductVal V))
    (specialUnitaryProductFrame_reconstruct B hB htr)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  have hz : ∀ a : SpecialUnitaryProductFrameIndex n K,
      smoothMatrixProductGeneratorDifferential f (specialUnitaryProductVal V)
        (specialUnitaryProductFrame a) = 0 := fun a => hzero a V
  simp only [hz, mul_zero, Finset.sum_const_zero] at h
  exact h.symm

/-- The actual product Haar Laplacian has exactly constant smooth kernel functions. -/
theorem smoothSpecialUnitaryProduct_laplacian_kernel_const {n K : ℕ} [NeZero n]
    (f : smoothMatrixProductFunctions n K)
    (hL : ∀ U : SpecialUnitaryProduct n K,
      derivationLaplacian (smoothSpecialUnitaryProductDerivative n K) f
        (specialUnitaryProductVal U) = 0)
    (U : SpecialUnitaryProduct n K) : f (specialUnitaryProductVal U) = f 1 := by
  let D := smoothSpecialUnitaryProductDerivative n K
  let J := smoothSpecialUnitaryProductIntegral n K
  have hibp (a : SpecialUnitaryProductFrameIndex n K) :
      J (f * D a (D a f)) = -J (D a f * D a f) := by
    exact smoothSpecialUnitaryProductIntegral_integration_by_parts
      (specialUnitaryProductFrame a)
      (fun i => congrFun (specialUnitaryProductFrame_skew a) i)
      (specialUnitaryProductFrame_trace a) f (D a f)
  have htotal : ∑ a : SpecialUnitaryProductFrameIndex n K, J (D a f * D a f) = 0 := by
    have hz : J (f * derivationLaplacian D f) = 0 := by
      change (∫ V : SpecialUnitaryProduct n K,
        f (specialUnitaryProductVal V) * derivationLaplacian D f (specialUnitaryProductVal V)
          ∂specialUnitaryProductHaar n K) = 0
      have hh (V : SpecialUnitaryProduct n K) :
          derivationLaplacian D f (specialUnitaryProductVal V) = 0 := hL V
      simp_rw [hh, mul_zero]
      simp
    rw [derivationLaplacian_apply, Finset.mul_sum, map_sum] at hz
    simp_rw [hibp] at hz
    simpa only [Finset.sum_neg_distrib, neg_eq_zero] using hz
  have hn (a : SpecialUnitaryProductFrameIndex n K) : 0 ≤ J (D a f * D a f) := by
    apply smoothSpecialUnitaryProductIntegral_nonneg
    intro V
    exact mul_self_nonneg _
  have heach (a : SpecialUnitaryProductFrameIndex n K) : J (D a f * D a f) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hn a)).mp htotal a (Finset.mem_univ a)
  apply specialUnitaryProduct_const_of_frame_derivative_zero f _ U
  intro a
  have hi : Integrable (fun V : SpecialUnitaryProduct n K =>
      (D a f (specialUnitaryProductVal V))^2) (specialUnitaryProductHaar n K) := by
    simp only [pow_two]
    exact integrable_smoothSpecialUnitaryProduct (D a f * D a f)
  have hz : (fun V : SpecialUnitaryProduct n K => (D a f (specialUnitaryProductVal V))^2)
      =ᵐ[specialUnitaryProductHaar n K] 0 := by
    apply (integral_eq_zero_iff_of_nonneg (fun V => sq_nonneg _) hi).mp
    simp only [pow_two]
    exact heach a
  have hz' : (fun V : SpecialUnitaryProduct n K => D a f (specialUnitaryProductVal V))
      =ᵐ[specialUnitaryProductHaar n K] 0 := by
    filter_upwards [hz] with V hV
    exact sq_eq_zero_iff.mp hV
  have hc : Continuous (fun V : SpecialUnitaryProduct n K => D a f (specialUnitaryProductVal V)) :=
    (smoothMatrixProductFunctions_contDiff (D a f)).continuous.comp
      (continuous_specialUnitaryProductVal n K)
  have hfzero := (hc.ae_eq_iff_eq (specialUnitaryProductHaar n K) continuous_const).mp hz'
  intro V
  exact congrFun hfzero V

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2MaximumPrinciple -/
section
open Filter Set
open scoped Topology

namespace BosonicLearn.Prop2

/-- A minimum on a left-hand time interval has nonpositive time derivative at
its rightmost point, including an endpoint minimum. -/
theorem derivative_nonpos_at_interval_minimum
    (f : ℝ → ℝ) (a t b d : ℝ) (hat : a < t) (htb : t ≤ b)
    (hmin : ∀ s ∈ Icc a b, f t ≤ f s) (hd : HasDerivAt f d t) : d ≤ 0 := by
  apply le_of_tendsto hd.tendsto_slope_zero_left
  have hnear : ∀ᶠ h : ℝ in 𝓝[<] 0, a - t < h :=
    (eventually_gt_nhds (by linarith : a - t < 0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hnear] with h hh hnear
  have hh0 : h < 0 := hh
  have hmem : t + h ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hval := hmin (t+h) hmem
  simp only [smul_eq_mul]
  exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr hh0.le) (sub_nonneg.mpr hval)

/-- Compact-space parabolic minimum principle. It suffices that the time
velocity is nonnegative at every spatial minimum. This interface applies to
finite-dimensional polynomial heat evolution without assuming a heat kernel. -/
theorem compact_parabolic_minimum_principle
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (u v : ℝ → X → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hu : ContinuousOn (fun p : ℝ × X => u p.1 p.2) (Icc 0 T ×ˢ univ))
    (hderiv : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivAt (fun s => u s x) (v t x) t)
    (hmin : ∀ t ∈ Ioc 0 T, ∀ x,
      (∀ y, u t x ≤ u t y) → 0 ≤ v t x)
    (hzero : ∀ x, 0 ≤ u 0 x) : ∀ x, 0 ≤ u T x := by
  intro x
  by_contra hneg
  have hx : u T x < 0 := lt_of_not_ge hneg
  let ε : ℝ := -u T x / (2 * (T + 1))
  have hε : 0 < ε := by
    exact div_pos (neg_pos.mpr hx) (by positivity)
  let w : ℝ × X → ℝ := fun p => u p.1 p.2 + ε * (p.1 + 1)
  have hwcont : ContinuousOn w (Icc 0 T ×ˢ univ) :=
    hu.add (by fun_prop)
  have hcompact : IsCompact (Icc (0 : ℝ) T ×ˢ (univ : Set X)) :=
    isCompact_Icc.prod isCompact_univ
  have hne : (Icc (0 : ℝ) T ×ˢ (univ : Set X)).Nonempty :=
    ⟨(0, x), ⟨⟨le_rfl, hT⟩, mem_univ _⟩⟩
  obtain ⟨p, hp, hpmin⟩ := hcompact.exists_isMinOn hne hwcont
  have hwt : w (T,x) < 0 := by
    dsimp [w, ε]
    have hTp : T + 1 ≠ 0 := by linarith
    field_simp
    nlinarith
  have hwp : w p < 0 := (hpmin ⟨⟨hT,le_rfl⟩,mem_univ x⟩).trans_lt hwt
  have hpt : 0 < p.1 := by
    by_contra hh
    have heq : p.1 = 0 := le_antisymm (le_of_not_gt hh) hp.1.1
    have hz := hzero p.2
    dsimp [w] at hwp
    rw [heq] at hwp
    nlinarith
  have hpI : p.1 ∈ Ioc 0 T := ⟨hpt,hp.1.2⟩
  have hspace : ∀ y, u p.1 p.2 ≤ u p.1 y := by
    intro y
    have h := hpmin (show (p.1,y) ∈ Icc 0 T ×ˢ (univ : Set X) from ⟨hp.1,mem_univ y⟩)
    dsimp [w] at h
    linarith
  have hvelocity := hmin p.1 hpI p.2 hspace
  have htime : ∀ s ∈ Icc 0 T, w p ≤ w (s,p.2) := by
    intro s hs
    exact hpmin ⟨hs,mem_univ _⟩
  have hwd : HasDerivAt (fun s => w (s,p.2)) (v p.1 p.2 + ε) p.1 := by
    simpa only [w, mul_one, id_eq] using (hderiv p.1 hpI p.2).fun_add
      (((hasDerivAt_id p.1).add_const 1).const_mul ε)
  have hnonpos := derivative_nonpos_at_interval_minimum (fun s => w (s,p.2)) 0 p.1 T
    (v p.1 p.2 + ε) hpt hp.1.2 htime hwd
  linarith

/-- The second derivative at a global minimum is nonnegative. The first
and second derivatives are supplied explicitly, which is convenient for
one-parameter group orbits. -/
theorem second_derivative_nonneg_at_minimum
    (f g : ℝ → ℝ) (c : ℝ)
    (hf : ∀ t : ℝ, HasDerivAt f (g t) t)
    (hg : HasDerivAt g c 0) (hmin : ∀ t : ℝ, f 0 ≤ f t) : 0 ≤ c := by
  have hlocal : IsLocalMin f 0 := Filter.Eventually.of_forall hmin
  have hg0 : g 0 = 0 := hlocal.hasDerivAt_eq_zero (hf 0)
  by_contra hh
  have hc : c < 0 := lt_of_not_ge hh
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, g t < 0 := by
    have hs := hg.tendsto_slope_zero_right.eventually (eventually_lt_nhds hc)
    filter_upwards [hs, self_mem_nhdsWithin] with t ht ht0
    simp only [zero_add, hg0, sub_zero, smul_eq_mul] at ht
    by_contra hnonneg
    exact (not_lt_of_ge (mul_nonneg (inv_nonneg.mpr ht0.le) (le_of_not_gt hnonneg))) ht
  obtain ⟨b, hb, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hanti : StrictAntiOn f (Icc 0 b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 b)
    · intro t ht
      exact (hf t).continuousAt.continuousWithinAt
    · intro t ht
      rw [(hf t).deriv]
      exact hsub (by simpa only [interior_Icc] using ht)
  exact (not_lt_of_ge (hmin b)) (hanti ⟨le_rfl,hb.le⟩ ⟨hb.le,le_rfl⟩ hb)

end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ProductSmoothMinimum -/
section
open scoped Matrix Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section

local instance productMinimumMatrixNormedAlgebraRat (n : ℕ) :
    NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _

/-- The product invariant derivative along any ambient exponential orbit. -/
theorem hasDerivAt_smoothMatrixProduct_orbit {n K : ℕ}
    (B A : MatrixProduct n K) (f : smoothMatrixProductFunctions n K) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (A * NormedSpace.exp (s • B)))
      (smoothRightMatrixProductDerivative B f (A * NormedSpace.exp (t • B))) t := by
  have hf := ((smoothMatrixProductFunctions_contDiff f).differentiable (by simp))
    (A * NormedSpace.exp (t • B))
  have he := (hasDerivAt_exp_smul_const B t).const_mul A
  simpa only [smoothRightMatrixProductDerivative_apply, rightMatrixProductDerivative,
    mul_assoc, Function.comp_def] using! hf.hasFDerivAt.comp_hasDerivAt t he

theorem smoothMatrixProduct_second_nonneg_at_orbit_minimum {n K : ℕ}
    (B A : MatrixProduct n K) (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0)
    (f : smoothMatrixProductFunctions n K)
    (hmin : ∀ V : SpecialUnitaryProduct n K,
      f A ≤ f (A * specialUnitaryProductVal V)) :
    0 ≤ smoothRightMatrixProductDerivative B (smoothRightMatrixProductDerivative B f) A := by
  apply second_derivative_nonneg_at_minimum
    (fun t => f (A * NormedSpace.exp (t • B)))
    (fun t => smoothRightMatrixProductDerivative B f (A * NormedSpace.exp (t • B)))
  · exact hasDerivAt_smoothMatrixProduct_orbit B A f
  · simpa using hasDerivAt_smoothMatrixProduct_orbit B A (smoothRightMatrixProductDerivative B f) 0
  · intro t
    have he : specialUnitaryProductVal (matrixProductSpecialUnitaryFlow B hB htr t) =
        NormedSpace.exp (t • B) := by
      rw [Pi.exp_def]
      rfl
    simpa only [he, zero_smul, NormedSpace.exp_zero, mul_one] using
      hmin (matrixProductSpecialUnitaryFlow B hB htr t)

theorem smoothSpecialUnitaryProduct_laplacian_nonneg_at_orbit_minimum
    (n K : ℕ) [NeZero n] (f : smoothMatrixProductFunctions n K)
    (A : MatrixProduct n K)
    (hmin : ∀ V : SpecialUnitaryProduct n K,
      f A ≤ f (A * specialUnitaryProductVal V)) :
    0 ≤ derivationLaplacian (smoothSpecialUnitaryProductDerivative n K) f A := by
  change 0 ≤ smoothMatrixProductEvaluation A
    (derivationLaplacian (smoothSpecialUnitaryProductDerivative n K) f)
  rw [derivationLaplacian_apply, map_sum]
  change 0 ≤ ∑ a : SpecialUnitaryProductFrameIndex n K,
    smoothRightMatrixProductDerivative (specialUnitaryProductFrame a)
      (smoothRightMatrixProductDerivative (specialUnitaryProductFrame a) f) A
  apply Finset.sum_nonneg
  intro a ha
  exact smoothMatrixProduct_second_nonneg_at_orbit_minimum (specialUnitaryProductFrame a) A
    (fun i => congrFun (specialUnitaryProductFrame_skew a) i)
    (specialUnitaryProductFrame_trace a) f hmin

/-- The true finite product Casimir heat equation preserves any initial lower bound. -/
theorem smoothSpecialUnitaryProduct_heat_preserves_lower
    (n K : ℕ) [NeZero n] (f : ℝ → smoothMatrixProductFunctions n K)
    (T c : ℝ) (hT : 0 ≤ T)
    (hcont : Continuous (fun p : ℝ × SpecialUnitaryProduct n K =>
      f p.1 (specialUnitaryProductVal p.2)))
    (hode : ∀ t ∈ Set.Ioc 0 T, ∀ U : SpecialUnitaryProduct n K,
      HasDerivAt (fun s => f s (specialUnitaryProductVal U))
        (derivationLaplacian (smoothSpecialUnitaryProductDerivative n K) (f t)
          (specialUnitaryProductVal U)) t)
    (hzero : ∀ U : SpecialUnitaryProduct n K, c ≤ f 0 (specialUnitaryProductVal U)) :
    ∀ U : SpecialUnitaryProduct n K, c ≤ f T (specialUnitaryProductVal U) := by
  have h := compact_parabolic_minimum_principle
    (fun (t : ℝ) (U : SpecialUnitaryProduct n K) => f t (specialUnitaryProductVal U) - c)
    (fun (t : ℝ) (U : SpecialUnitaryProduct n K) =>
      derivationLaplacian (smoothSpecialUnitaryProductDerivative n K) (f t)
        (specialUnitaryProductVal U)) T hT
    (hcont.sub continuous_const).continuousOn
    (fun t ht U => (hode t ht U).sub_const c) (by
      intro t ht U hmin
      apply smoothSpecialUnitaryProduct_laplacian_nonneg_at_orbit_minimum n K (f t)
        (specialUnitaryProductVal U)
      intro V
      have hh := hmin (U*V)
      exact (sub_le_sub_iff_right c).mp hh)
    (fun U => sub_nonneg.mpr (hzero U))
  exact fun U => sub_nonneg.mp (h U)

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ProductPolynomialHeat -/
section
open MeasureTheory Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- The polynomial-class map into the genuine finite Hilbert space. -/
def matrixProductPolynomialHilbertImage (n K d : ℕ) :
    matrixProductPolynomialSpace n K d →ₗ[ℝ] specialUnitaryProductPolynomialHilbert n K d :=
  (continuousL2Equiv (specialUnitaryProductHaar n K)
    (specialUnitaryProductPolynomialSpace n K d)).toLinearMap.comp
      (matrixProductPolynomialRestriction n K d).rangeRestrict

/-- Choose an ambient polynomial representative linearly. -/
def matrixProductPolynomialSection (n K d : ℕ) :
    specialUnitaryProductPolynomialSpace n K d →ₗ[ℝ] matrixProductPolynomialSpace n K d :=
  Classical.choose ((matrixProductPolynomialRestriction n K d).rangeRestrict.exists_rightInverse_of_surjective
    (matrixProductPolynomialRestriction n K d).range_rangeRestrict)

@[simp] theorem matrixProductPolynomialSection_rightInverse (n K d : ℕ)
    (f : specialUnitaryProductPolynomialSpace n K d) :
    (matrixProductPolynomialRestriction n K d).rangeRestrict
      (matrixProductPolynomialSection n K d f) = f :=
  LinearMap.congr_fun (Classical.choose_spec
    ((matrixProductPolynomialRestriction n K d).rangeRestrict.exists_rightInverse_of_surjective
      (matrixProductPolynomialRestriction n K d).range_rangeRestrict)) f

/-- A linear polynomial representative for each Hilbert function. -/
def matrixProductPolynomialHilbertLift (n K d : ℕ) :
    specialUnitaryProductPolynomialHilbert n K d →ₗ[ℝ] matrixProductPolynomialSpace n K d :=
  (matrixProductPolynomialSection n K d).comp
    (continuousL2Equiv (specialUnitaryProductHaar n K)
      (specialUnitaryProductPolynomialSpace n K d)).symm.toLinearMap

/-- The same representative in the ambient smooth-function algebra. -/
def specialUnitaryProductPolynomialSmoothLift (n K d : ℕ) :
    specialUnitaryProductPolynomialHilbert n K d →ₗ[ℝ] smoothMatrixProductFunctions n K :=
  (matrixProductPolynomialSpace n K d).subtype.comp (matrixProductPolynomialHilbertLift n K d)

@[simp] theorem matrixProductPolynomialHilbertImage_lift {n K d : ℕ}
    (f : specialUnitaryProductPolynomialHilbert n K d) :
    matrixProductPolynomialHilbertImage n K d (matrixProductPolynomialHilbertLift n K d f) = f :=
by
  let e := continuousL2Equiv (specialUnitaryProductHaar n K) (specialUnitaryProductPolynomialSpace n K d)
  exact (congrArg e (matrixProductPolynomialSection_rightInverse n K d (e.symm f))).trans
    (e.apply_symm_apply f)

@[simp] theorem specialUnitaryProductPolynomialSmoothLift_restrict {n K d : ℕ}
    (f : specialUnitaryProductPolynomialHilbert n K d) :
    smoothSpecialUnitaryProductRestriction n K (specialUnitaryProductPolynomialSmoothLift n K d f) =
      continuousL2Representative (specialUnitaryProductHaar n K)
        (specialUnitaryProductPolynomialSpace n K d) f :=
by
  exact congrArg Subtype.val (matrixProductPolynomialSection_rightInverse n K d
    ((continuousL2Equiv (specialUnitaryProductHaar n K)
      (specialUnitaryProductPolynomialSpace n K d)).symm f))

@[simp] theorem matrixProductPolynomialHilbertImage_representative {n K d : ℕ}
    (f : matrixProductPolynomialSpace n K d) :
    continuousL2Representative (specialUnitaryProductHaar n K)
        (specialUnitaryProductPolynomialSpace n K d) (matrixProductPolynomialHilbertImage n K d f) =
      matrixProductPolynomialRestriction n K d f :=
  continuousL2Representative_equiv _ _ ((matrixProductPolynomialRestriction n K d).rangeRestrict f)

@[simp] theorem specialUnitaryProductPolynomialHilbertDerivative_image {n K d : ℕ}
    (B : MatrixProduct n K) (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0)
    (f : matrixProductPolynomialSpace n K d) :
    specialUnitaryProductPolynomialHilbertDerivative n K d B hB htr
      (matrixProductPolynomialHilbertImage n K d f) =
      matrixProductPolynomialHilbertImage n K d (matrixProductPolynomialDerivative n K d B f) :=
by
  change continuousL2Operator _ _ _ (continuousL2Equiv _ _ _) = _
  rw [continuousL2Operator_equiv]
  apply (continuousL2Equiv (specialUnitaryProductHaar n K)
    (specialUnitaryProductPolynomialSpace n K d)).congr_arg
  exact Subtype.ext (specialUnitaryProductPolynomialDerivative_apply_image B hB htr f)


/-- The ambient polynomial Laplacian, which preserves every finite degree. -/
def matrixProductPolynomialLaplacian (n K d : ℕ) [NeZero n] :
    matrixProductPolynomialSpace n K d →ₗ[ℝ] matrixProductPolynomialSpace n K d :=
  ∑ a : SpecialUnitaryProductFrameIndex n K,
    let D := matrixProductPolynomialDerivative n K d (specialUnitaryProductFrame a)
    D.comp D

@[simp] theorem matrixProductPolynomialLaplacian_coe {n K d : ℕ} [NeZero n]
    (f : matrixProductPolynomialSpace n K d) :
    (matrixProductPolynomialLaplacian n K d f : smoothMatrixProductFunctions n K) =
      derivationLaplacian (smoothSpecialUnitaryProductDerivative n K) f := by
  change (matrixProductPolynomialSpace n K d).subtype
    ((matrixProductPolynomialLaplacian n K d) f) = _
  simp only [matrixProductPolynomialLaplacian, LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  rw [derivationLaplacian_apply]
  apply Finset.sum_congr rfl
  intro a ha
  rfl

@[simp] theorem specialUnitaryProductPolynomialHilbertLaplacian_image {n K d : ℕ} [NeZero n]
    (f : matrixProductPolynomialSpace n K d) :
    specialUnitaryProductPolynomialHilbertLaplacian n K d
      (matrixProductPolynomialHilbertImage n K d f) =
      matrixProductPolynomialHilbertImage n K d (matrixProductPolynomialLaplacian n K d f) := by
  simp only [specialUnitaryProductPolynomialHilbertLaplacian, matrixProductPolynomialLaplacian,
    LinearMap.sum_apply, LinearMap.comp_apply, specialUnitaryProductPolynomialHilbertDerivative_image,
    map_sum]

/-- The quotient Laplacian is the actual smooth group Laplacian of any chosen representative. -/
theorem specialUnitaryProductPolynomialLaplacian_representative {n K d : ℕ} [NeZero n]
    (f : specialUnitaryProductPolynomialHilbert n K d) :
    continuousL2Representative (specialUnitaryProductHaar n K)
      (specialUnitaryProductPolynomialSpace n K d)
      (specialUnitaryProductPolynomialHilbertLaplacian n K d f) =
    smoothSpecialUnitaryProductRestriction n K
      (derivationLaplacian (smoothSpecialUnitaryProductDerivative n K)
        (specialUnitaryProductPolynomialSmoothLift n K d f)) := by
  have h := congrArg
    (continuousL2Representative (specialUnitaryProductHaar n K)
      (specialUnitaryProductPolynomialSpace n K d))
    (specialUnitaryProductPolynomialHilbertLaplacian_image (matrixProductPolynomialHilbertLift n K d f))
  rw [matrixProductPolynomialHilbertImage_lift, matrixProductPolynomialHilbertImage_representative] at h
  exact h.trans (congrArg (smoothSpecialUnitaryProductRestriction n K)
    (matrixProductPolynomialLaplacian_coe (matrixProductPolynomialHilbertLift n K d f)))

/-- An actual ambient smooth representative of finite polynomial heat. -/
def specialUnitaryProductSmoothHeat (n K d : ℕ) [NeZero n]
    (f : specialUnitaryProductPolynomialHilbert n K d) (t : ℝ) : smoothMatrixProductFunctions n K :=
  specialUnitaryProductPolynomialSmoothLift n K d (specialUnitaryProductPolynomialHeat n K d t f)

/-- The heat trajectory is continuous as a continuous function on the entire group. -/
theorem specialUnitaryProductSmoothHeat_continuous {n K d : ℕ} [NeZero n]
    (f : specialUnitaryProductPolynomialHilbert n K d) :
    Continuous (fun t => smoothSpecialUnitaryProductRestriction n K
      (specialUnitaryProductSmoothHeat n K d f t)) := by
  simp only [specialUnitaryProductSmoothHeat, specialUnitaryProductPolynomialSmoothLift_restrict]
  exact (continuousL2RepresentativeCLM (specialUnitaryProductHaar n K)
    (specialUnitaryProductPolynomialSpace n K d)).continuous.comp
      (continuous_iff_continuousAt.mpr fun t =>
        (specialUnitaryProductPolynomialHeat_hasDerivAt n K d f t).continuousAt)

/-- Pointwise heat equation for the actual invariant matrix Laplacian. -/
theorem specialUnitaryProductSmoothHeat_hasDerivAt {n K d : ℕ} [NeZero n]
    (f : specialUnitaryProductPolynomialHilbert n K d) (t : ℝ)
    (U : SpecialUnitaryProduct n K) :
    HasDerivAt (fun s => specialUnitaryProductSmoothHeat n K d f s (specialUnitaryProductVal U))
      (derivationLaplacian (smoothSpecialUnitaryProductDerivative n K)
        (specialUnitaryProductSmoothHeat n K d f t) (specialUnitaryProductVal U)) t := by
  let E := (ContinuousMap.evalCLM ℝ U).comp
    (continuousL2RepresentativeCLM (specialUnitaryProductHaar n K)
      (specialUnitaryProductPolynomialSpace n K d))
  have h := E.hasFDerivAt.comp_hasDerivAt t (specialUnitaryProductPolynomialHeat_hasDerivAt n K d f t)
  have heq (s : ℝ) : E (specialUnitaryProductPolynomialHeat n K d s f) =
      specialUnitaryProductSmoothHeat n K d f s (specialUnitaryProductVal U) := by
    exact congrArg (fun g : C(SpecialUnitaryProduct n K, ℝ) => g U)
      (specialUnitaryProductPolynomialSmoothLift_restrict
        (specialUnitaryProductPolynomialHeat n K d s f)).symm
  dsimp only [Function.comp_def] at h
  rw [show (fun s => E (specialUnitaryProductPolynomialHeat n K d s f)) = _ from funext heq] at h
  have hd := congrArg (fun g : C(SpecialUnitaryProduct n K, ℝ) => g U)
    (specialUnitaryProductPolynomialLaplacian_representative (specialUnitaryProductPolynomialHeat n K d t f))
  change E (specialUnitaryProductPolynomialHilbertLaplacian n K d
    (specialUnitaryProductPolynomialHeat n K d t f)) =
      derivationLaplacian (smoothSpecialUnitaryProductDerivative n K)
        (specialUnitaryProductSmoothHeat n K d f t) (specialUnitaryProductVal U) at hd
  rw [hd] at h
  exact h

/-- The constant polynomial belongs to every degree, including degree zero. -/
def matrixProductPolynomialOne (n K d : ℕ) : matrixProductPolynomialSpace n K d :=
  ⟨1, by
    have h := finiteMonomial_mem (matrixProductPolynomialGenerator n K) d (fun _ => none)
    simpa only [matrixProductPolynomialSpace, finiteMonomial, matrixProductPolynomialGenerator, Finset.prod_const_one] using h⟩

def specialUnitaryProductPolynomialOne (n K d : ℕ) : specialUnitaryProductPolynomialHilbert n K d :=
  matrixProductPolynomialHilbertImage n K d (matrixProductPolynomialOne n K d)

@[simp] theorem specialUnitaryProductPolynomialOne_representative (n K d : ℕ) :
    continuousL2Representative (specialUnitaryProductHaar n K)
      (specialUnitaryProductPolynomialSpace n K d) (specialUnitaryProductPolynomialOne n K d) = 1 := by
  rw [specialUnitaryProductPolynomialOne, matrixProductPolynomialHilbertImage_representative]
  rfl

@[simp] theorem specialUnitaryProductPolynomialOne_laplacian (n K d : ℕ) [NeZero n] :
    specialUnitaryProductPolynomialHilbertLaplacian n K d
      (specialUnitaryProductPolynomialOne n K d) = 0 := by
  rw [specialUnitaryProductPolynomialOne, specialUnitaryProductPolynomialHilbertLaplacian_image]
  have hz : matrixProductPolynomialLaplacian n K d (matrixProductPolynomialOne n K d) = 0 := by
    apply Subtype.ext
    rw [matrixProductPolynomialLaplacian_coe]
    change derivationLaplacian (smoothSpecialUnitaryProductDerivative n K) 1 = 0
    rw [derivationLaplacian_apply]
    apply Finset.sum_eq_zero
    intro a ha
    have h1 : smoothSpecialUnitaryProductDerivative n K a 1 = 0 :=
      (smoothRightMatrixProductDerivation (specialUnitaryProductFrame a)).map_one_eq_zero
    rw [h1, map_zero]
  rw [hz, map_zero]

theorem specialUnitaryProductPolynomialOne_inner (n K d : ℕ)
    (f : specialUnitaryProductPolynomialHilbert n K d) :
    inner ℝ (specialUnitaryProductPolynomialOne n K d) f =
      ∫ U, continuousL2Representative (specialUnitaryProductHaar n K)
        (specialUnitaryProductPolynomialSpace n K d) f U ∂specialUnitaryProductHaar n K := by
  rw [continuousL2_inner, specialUnitaryProductPolynomialOne_representative]
  simp

@[simp] theorem specialUnitaryProductPolynomialOne_norm (n K d : ℕ) :
    inner ℝ (specialUnitaryProductPolynomialOne n K d) (specialUnitaryProductPolynomialOne n K d) = 1 := by
  rw [specialUnitaryProductPolynomialOne_inner, specialUnitaryProductPolynomialOne_representative]
  simp

/-- The concrete polynomial Laplacian has exactly the constants as its kernel. -/
theorem specialUnitaryProductPolynomialHilbertLaplacian_kernel {n K d : ℕ} [NeZero n]
    (f : specialUnitaryProductPolynomialHilbert n K d)
    (hf : specialUnitaryProductPolynomialHilbertLaplacian n K d f = 0) :
    ∃ c : ℝ, f = c • specialUnitaryProductPolynomialOne n K d := by
  let p := specialUnitaryProductPolynomialSmoothLift n K d f
  have hL : ∀ U : SpecialUnitaryProduct n K,
      derivationLaplacian (smoothSpecialUnitaryProductDerivative n K) p (specialUnitaryProductVal U) = 0 := by
    intro U
    have h := congrArg (fun g : C(SpecialUnitaryProduct n K, ℝ) => g U)
      (specialUnitaryProductPolynomialLaplacian_representative f)
    rw [hf, map_zero] at h
    exact h.symm
  refine ⟨p 1, ?_⟩
  apply (continuousL2Equiv (specialUnitaryProductHaar n K)
    (specialUnitaryProductPolynomialSpace n K d)).symm.injective
  apply Subtype.ext
  change continuousL2Representative (specialUnitaryProductHaar n K)
    (specialUnitaryProductPolynomialSpace n K d) f =
      continuousL2Representative (specialUnitaryProductHaar n K)
        (specialUnitaryProductPolynomialSpace n K d) ((p 1) • specialUnitaryProductPolynomialOne n K d)
  rw [map_smul, specialUnitaryProductPolynomialOne_representative]
  ext U
  simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
  change continuousL2Representative (specialUnitaryProductHaar n K)
    (specialUnitaryProductPolynomialSpace n K d) f U = p 1
  rw [← specialUnitaryProductPolynomialSmoothLift_restrict]
  exact smoothSpecialUnitaryProduct_laplacian_kernel_const p hL U

/-- Heat converges in the uniform norm to its original Haar mean. -/
theorem specialUnitaryProductSmoothHeat_tendsto_mean {n K d : ℕ} [NeZero n]
    (f : specialUnitaryProductPolynomialHilbert n K d) :
    Tendsto (fun t => smoothSpecialUnitaryProductRestriction n K
      (specialUnitaryProductSmoothHeat n K d f t)) atTop
      (𝓝 ((∫ U, continuousL2Representative (specialUnitaryProductHaar n K)
        (specialUnitaryProductPolynomialSpace n K d) f U ∂specialUnitaryProductHaar n K) •
          (1 : C(SpecialUnitaryProduct n K, ℝ)))) := by
  have h := finiteSelfAdjointHeat_tendsto_constant
    (specialUnitaryProductPolynomialHilbertLaplacian n K d)
    (specialUnitaryProductPolynomialHilbertLaplacian_symmetric n K d)
    (specialUnitaryProductPolynomialHilbertLaplacian_nonpos n K d)
    (specialUnitaryProductPolynomialOne n K d) (specialUnitaryProductPolynomialOne_norm n K d)
    (specialUnitaryProductPolynomialOne_laplacian n K d)
    (fun q hq => specialUnitaryProductPolynomialHilbertLaplacian_kernel q hq) f
  have h' := (continuousL2RepresentativeCLM (specialUnitaryProductHaar n K)
    (specialUnitaryProductPolynomialSpace n K d)).continuous.tendsto
      ((inner ℝ (specialUnitaryProductPolynomialOne n K d) f) • specialUnitaryProductPolynomialOne n K d) |>.comp h
  simpa only [specialUnitaryProductSmoothHeat, specialUnitaryProductPolynomialHeat,
    specialUnitaryProductPolynomialSmoothLift_restrict, continuousL2RepresentativeCLM,
    LinearMap.coe_toContinuousLinearMap', map_smul, specialUnitaryProductPolynomialOne_representative,
    specialUnitaryProductPolynomialOne_inner, Function.comp_def] using! h'

/-- Joint continuity on time and the compact product group. -/
theorem specialUnitaryProductSmoothHeat_joint_continuous {n K d : ℕ} [NeZero n]
    (f : specialUnitaryProductPolynomialHilbert n K d) :
    Continuous (fun p : ℝ × SpecialUnitaryProduct n K =>
      specialUnitaryProductSmoothHeat n K d f p.1 (specialUnitaryProductVal p.2)) :=
  continuous_eval.comp
    (((specialUnitaryProductSmoothHeat_continuous f).comp continuous_fst).prodMk continuous_snd)

@[simp] theorem specialUnitaryProductSmoothHeat_zero {n K d : ℕ} [NeZero n]
    (f : specialUnitaryProductPolynomialHilbert n K d) :
    smoothSpecialUnitaryProductRestriction n K (specialUnitaryProductSmoothHeat n K d f 0) =
      continuousL2Representative (specialUnitaryProductHaar n K)
        (specialUnitaryProductPolynomialSpace n K d) f := by
  simp only [specialUnitaryProductSmoothHeat, specialUnitaryProductPolynomialHeat,
    finiteSelfAdjointHeat_zero, specialUnitaryProductPolynomialSmoothLift_restrict]

/-- The actual finite-dimensional polynomial heat preserves each pointwise lower bound. -/
theorem specialUnitaryProductSmoothHeat_preserves_lower {n K d : ℕ} [NeZero n]
    (f : specialUnitaryProductPolynomialHilbert n K d) (c : ℝ)
    (hf : ∀ U, c ≤ continuousL2Representative (specialUnitaryProductHaar n K)
      (specialUnitaryProductPolynomialSpace n K d) f U) (t : ℝ) (ht : 0 ≤ t) :
    ∀ U : SpecialUnitaryProduct n K,
      c ≤ specialUnitaryProductSmoothHeat n K d f t (specialUnitaryProductVal U) := by
  apply smoothSpecialUnitaryProduct_heat_preserves_lower n K
    (specialUnitaryProductSmoothHeat n K d f) t c ht
    (specialUnitaryProductSmoothHeat_joint_continuous f)
    (fun s hs U => specialUnitaryProductSmoothHeat_hasDerivAt f s U)
  intro U
  have h := congrArg (fun g : C(SpecialUnitaryProduct n K, ℝ) => g U)
    (specialUnitaryProductSmoothHeat_zero f)
  exact (hf U).trans_eq h.symm

/-- Polynomial heat preserves the actual Haar integral exactly. -/
theorem specialUnitaryProductSmoothHeat_integral {n K d : ℕ} [NeZero n]
    (f : specialUnitaryProductPolynomialHilbert n K d) (t : ℝ) :
    (∫ U : SpecialUnitaryProduct n K,
      specialUnitaryProductSmoothHeat n K d f t (specialUnitaryProductVal U)
        ∂specialUnitaryProductHaar n K) =
    ∫ U, continuousL2Representative (specialUnitaryProductHaar n K)
      (specialUnitaryProductPolynomialSpace n K d) f U ∂specialUnitaryProductHaar n K := by
  have h := finiteSelfAdjointHeat_inner_kernel
    (specialUnitaryProductPolynomialHilbertLaplacian n K d)
    (specialUnitaryProductPolynomialHilbertLaplacian_symmetric n K d)
    (specialUnitaryProductPolynomialOne n K d)
    (specialUnitaryProductPolynomialOne_laplacian n K d) f t
  rw [specialUnitaryProductPolynomialOne_inner, specialUnitaryProductPolynomialOne_inner] at h
  have heq (U : SpecialUnitaryProduct n K) :
      specialUnitaryProductSmoothHeat n K d f t (specialUnitaryProductVal U) =
      continuousL2Representative (specialUnitaryProductHaar n K)
        (specialUnitaryProductPolynomialSpace n K d)
        (specialUnitaryProductPolynomialHeat n K d t f) U :=
    congrArg (fun g : C(SpecialUnitaryProduct n K, ℝ) => g U)
      (specialUnitaryProductPolynomialSmoothLift_restrict
        (specialUnitaryProductPolynomialHeat n K d t f))
  simp_rw [heq]
  exact h

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2PositiveClamp -/
section
open scoped ContDiff

namespace BosonicLearn.Prop2
noncomputable section

/-- A smooth positive replacement for the identity, equal to the identity on
`[2a,∞)`. It allows logarithms of ambient representatives positive on SU. -/
def smoothPositiveClamp (a x : ℝ) : ℝ :=
  a + Real.smoothTransition ((x-a)/a) * (x-a)

theorem smoothPositiveClamp_smooth (a : ℝ) : ContDiff ℝ ∞ (smoothPositiveClamp a) := by
  unfold smoothPositiveClamp
  exact contDiff_const.add
    ((Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const a)).mul
      (contDiff_id.sub contDiff_const))

theorem smoothPositiveClamp_lower (a : ℝ) (ha : 0 < a) (x : ℝ) :
    a ≤ smoothPositiveClamp a x := by
  by_cases h : x ≤ a
  · have hz : Real.smoothTransition ((x-a)/a) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) ha.le)
    simp [smoothPositiveClamp, hz]
  · dsimp [smoothPositiveClamp]
    have hh := mul_nonneg (Real.smoothTransition.nonneg ((x-a)/a))
      (sub_nonneg.mpr (le_of_not_ge h))
    linarith

theorem smoothPositiveClamp_eq (a : ℝ) (ha : 0 < a) {x : ℝ} (hx : 2*a ≤ x) :
    smoothPositiveClamp a x = x := by
  have hh : 1 ≤ (x-a)/a := (le_div_iff₀ ha).mpr (by linarith)
  simp [smoothPositiveClamp, Real.smoothTransition.one_of_one_le hh]


end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ProductSmoothPositive -/
section
open Filter Set
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff

namespace BosonicLearn.Prop2
noncomputable section

/-- Exponentiation in the actual smooth matrix function algebra. -/
def smoothMatrixProductExp {n K : ℕ} (f : smoothMatrixProductFunctions n K) : smoothMatrixProductFunctions n K :=
  ⟨fun A => Real.exp (f A), (smoothMatrixProductFunctions_contDiff f).exp⟩

def smoothMatrixProductLog {n K : ℕ} (f : smoothMatrixProductFunctions n K) (hf : ∀ A, f A ≠ 0) :
    smoothMatrixProductFunctions n K :=
  ⟨fun A => Real.log (f A), (smoothMatrixProductFunctions_contDiff f).log hf⟩

def smoothMatrixProductPositive {n K : ℕ} (a : ℝ) (f : smoothMatrixProductFunctions n K) : smoothMatrixProductFunctions n K :=
  ⟨fun A => smoothPositiveClamp a (f A),
    (smoothPositiveClamp_smooth a).comp (smoothMatrixProductFunctions_contDiff f)⟩

@[simp] theorem smoothMatrixProductExp_apply {n K : ℕ} (f : smoothMatrixProductFunctions n K) (A) :
    smoothMatrixProductExp f A = Real.exp (f A) := rfl

@[simp] theorem smoothMatrixProductLog_apply {n K : ℕ} (f : smoothMatrixProductFunctions n K) (hf) (A) :
    smoothMatrixProductLog f hf A = Real.log (f A) := rfl

theorem smoothMatrixProductDerivative_exp {n K : ℕ} (B : MatrixProduct n K)
    (f : smoothMatrixProductFunctions n K) :
    smoothRightMatrixProductDerivative B (smoothMatrixProductExp f) =
      smoothMatrixProductExp f * smoothRightMatrixProductDerivative B f := by
  apply Subtype.ext
  funext A
  change fderiv ℝ (fun X => Real.exp (f X)) A (A*B) =
    Real.exp (f A) * fderiv ℝ (f : MatrixProduct n K → ℝ) A (A*B)
  rw [fderiv_exp ((smoothMatrixProductFunctions_contDiff f).differentiable (by simp) A)]
  rfl

theorem smoothMatrixProductDerivative_log {n K : ℕ} (B : MatrixProduct n K)
    (f : smoothMatrixProductFunctions n K) (hf : ∀ A, f A ≠ 0) (A : MatrixProduct n K) :
    smoothRightMatrixProductDerivative B (smoothMatrixProductLog f hf) A =
      (f A)⁻¹ * smoothRightMatrixProductDerivative B f A := by
  change fderiv ℝ (fun X => Real.log (f X)) A (A*B) =
    (f A)⁻¹ * fderiv ℝ (f : MatrixProduct n K → ℝ) A (A*B)
  rw [fderiv.log ((smoothMatrixProductFunctions_contDiff f).differentiable (by simp) A) (hf A)]
  rfl

/-- Logarithmic differentiation in multiplicative form, valid globally. -/
theorem smoothMatrixProductDerivative_log_chain {n K : ℕ} (B : MatrixProduct n K)
    (f : smoothMatrixProductFunctions n K) (hf : ∀ A, f A ≠ 0) :
    smoothRightMatrixProductDerivative B f =
      f * smoothRightMatrixProductDerivative B (smoothMatrixProductLog f hf) := by
  apply Subtype.ext
  funext A
  change smoothRightMatrixProductDerivative B f A =
    f A * smoothRightMatrixProductDerivative B (smoothMatrixProductLog f hf) A
  rw [smoothMatrixProductDerivative_log, ← mul_assoc, mul_inv_cancel₀ (hf A), one_mul]

/-- Equality of smooth ambient representatives on the group is preserved by
any tangent invariant derivative. -/
theorem smoothMatrixProductDerivative_eq_on_group {n K : ℕ}
    (B : MatrixProduct n K) (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0)
    (f g : smoothMatrixProductFunctions n K)
    (heq : ∀ U : SpecialUnitaryProduct n K,
      f (specialUnitaryProductVal U) = g (specialUnitaryProductVal U))
    (U : SpecialUnitaryProduct n K) :
    smoothRightMatrixProductDerivative B f (specialUnitaryProductVal U) =
      smoothRightMatrixProductDerivative B g (specialUnitaryProductVal U) := by
  have hf := hasDerivAt_rightMatrixProductDerivative B hB htr f
    ((smoothMatrixProductFunctions_contDiff f).of_le (by simp)) 0 U
  have hg := hasDerivAt_rightMatrixProductDerivative B hB htr g
    ((smoothMatrixProductFunctions_contDiff g).of_le (by simp)) 0 U
  have hfun : (fun s => f (specialUnitaryProductVal (U * matrixProductSpecialUnitaryFlow B hB htr s))) =
      (fun s => g (specialUnitaryProductVal (U * matrixProductSpecialUnitaryFlow B hB htr s))) :=
    funext (fun s => heq _)
  rw [hfun] at hf
  have h := hf.unique hg
  have hzero : matrixProductSpecialUnitaryFlow B hB htr 0 = 1 := by
    funext i
    apply Subtype.ext
    simp [matrixProductSpecialUnitaryFlow, skewHermitianSpecialUnitaryFlow]
  rw [hzero, mul_one] at h
  exact h

theorem smoothMatrixProductPositive_lower {n K : ℕ} (a : ℝ) (ha : 0 < a)
    (f : smoothMatrixProductFunctions n K) (A : MatrixProduct n K) :
    a ≤ smoothMatrixProductPositive a f A := smoothPositiveClamp_lower a ha (f A)

theorem smoothMatrixProductPositive_ne_zero {n K : ℕ} (a : ℝ) (ha : 0 < a)
    (f : smoothMatrixProductFunctions n K) (A : MatrixProduct n K) :
    smoothMatrixProductPositive a f A ≠ 0 :=
  ne_of_gt (ha.trans_le (smoothMatrixProductPositive_lower a ha f A))

theorem smoothMatrixProductPositive_eq_on_group {n K : ℕ} (a : ℝ) (ha : 0 < a)
    (f : smoothMatrixProductFunctions n K)
    (hf : ∀ U : SpecialUnitaryProduct n K, 2*a ≤ f (specialUnitaryProductVal U))
    (U : SpecialUnitaryProduct n K) :
    smoothMatrixProductPositive a f (specialUnitaryProductVal U) = f (specialUnitaryProductVal U) :=
  smoothPositiveClamp_eq a ha (hf U)

theorem smoothMatrixProductPositive_derivative_eq_on_group {n K : ℕ}
    (a : ℝ) (ha : 0 < a) (f : smoothMatrixProductFunctions n K)
    (hf : ∀ U : SpecialUnitaryProduct n K, 2*a ≤ f (specialUnitaryProductVal U))
    (B : MatrixProduct n K) (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0)
    (U : SpecialUnitaryProduct n K) :
    smoothRightMatrixProductDerivative B (smoothMatrixProductPositive a f) (specialUnitaryProductVal U) =
      smoothRightMatrixProductDerivative B f (specialUnitaryProductVal U) :=
  smoothMatrixProductDerivative_eq_on_group B hB htr _ _
    (smoothMatrixProductPositive_eq_on_group a ha f hf) U

theorem smoothMatrixProductPositive_laplacian_eq_on_group {n K : ℕ} [NeZero n]
    (a : ℝ) (ha : 0 < a) (f : smoothMatrixProductFunctions n K)
    (hf : ∀ U : SpecialUnitaryProduct n K, 2*a ≤ f (specialUnitaryProductVal U))
    (U : SpecialUnitaryProduct n K) :
    derivationLaplacian (smoothSpecialUnitaryProductDerivative n K)
      (smoothMatrixProductPositive a f) (specialUnitaryProductVal U) =
    derivationLaplacian (smoothSpecialUnitaryProductDerivative n K) f (specialUnitaryProductVal U) := by
  change smoothMatrixProductEvaluation (specialUnitaryProductVal U)
    (derivationLaplacian (smoothSpecialUnitaryProductDerivative n K) (smoothMatrixProductPositive a f)) =
    smoothMatrixProductEvaluation (specialUnitaryProductVal U)
      (derivationLaplacian (smoothSpecialUnitaryProductDerivative n K) f)
  simp only [derivationLaplacian_apply, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply smoothMatrixProductDerivative_eq_on_group (specialUnitaryProductFrame b)
    (fun i => congrFun (specialUnitaryProductFrame_skew b) i)
    (specialUnitaryProductFrame_trace b)
  intro V
  exact smoothMatrixProductPositive_derivative_eq_on_group a ha f hf
    (specialUnitaryProductFrame b) (fun i => congrFun (specialUnitaryProductFrame_skew b) i)
    (specialUnitaryProductFrame_trace b) V

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ProductHeatODE -/
section
open Filter Set
open scoped Topology Matrix Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section

/-- Clamping a positive heat trajectory changes no time derivative on positive times. -/
theorem clamped_product_heat_hasDerivAt {n K : ℕ} [NeZero n]
    (p : ℝ → smoothMatrixProductFunctions n K) (a : ℝ) (ha : 0 < a)
    (hp : ∀ s : ℝ, 0 ≤ s → ∀ U : SpecialUnitaryProduct n K,
      2*a ≤ p s (specialUnitaryProductVal U))
    (htime : ∀ t : ℝ, 0 < t → ∀ U : SpecialUnitaryProduct n K,
      HasDerivAt (fun s => p s (specialUnitaryProductVal U))
        (derivationLaplacian (smoothSpecialUnitaryProductDerivative n K) (p t)
          (specialUnitaryProductVal U)) t)
    (t : ℝ) (ht : 0 < t) (U : SpecialUnitaryProduct n K) :
    HasDerivAt (fun s => smoothMatrixProductPositive a (p s) (specialUnitaryProductVal U))
      (derivationLaplacian (smoothSpecialUnitaryProductDerivative n K)
        (smoothMatrixProductPositive a (p t)) (specialUnitaryProductVal U)) t := by
  have heq : (fun s => smoothMatrixProductPositive a (p s) (specialUnitaryProductVal U))
      =ᶠ[𝓝 t] (fun s => p s (specialUnitaryProductVal U)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact smoothMatrixProductPositive_eq_on_group a ha (p s) (hp s hs.le) U
  have h := (htime t ht U).congr_of_eventuallyEq heq
  rw [smoothMatrixProductPositive_laplacian_eq_on_group a ha (p t) (hp t ht.le) U]
  exact h

/-- The same restriction argument preserves the differentiated time equation;
its right side contains the actual third-order spatial derivative DᵢL. -/
theorem clamped_product_heat_derivative_hasDerivAt {n K : ℕ} [NeZero n]
    (p : ℝ → smoothMatrixProductFunctions n K) (a : ℝ) (ha : 0 < a)
    (hp : ∀ s : ℝ, 0 ≤ s → ∀ U : SpecialUnitaryProduct n K,
      2*a ≤ p s (specialUnitaryProductVal U))
    (htime : ∀ t : ℝ, 0 < t → ∀ b : SpecialUnitaryProductFrameIndex n K,
      ∀ U : SpecialUnitaryProduct n K,
      HasDerivAt (fun s => smoothSpecialUnitaryProductDerivative n K b (p s)
          (specialUnitaryProductVal U))
        (smoothSpecialUnitaryProductDerivative n K b
          (derivationLaplacian (smoothSpecialUnitaryProductDerivative n K) (p t))
          (specialUnitaryProductVal U)) t)
    (t : ℝ) (ht : 0 < t) (b : SpecialUnitaryProductFrameIndex n K)
    (U : SpecialUnitaryProduct n K) :
    HasDerivAt (fun s => smoothSpecialUnitaryProductDerivative n K b
        (smoothMatrixProductPositive a (p s)) (specialUnitaryProductVal U))
      (smoothSpecialUnitaryProductDerivative n K b
        (derivationLaplacian (smoothSpecialUnitaryProductDerivative n K)
          (smoothMatrixProductPositive a (p t))) (specialUnitaryProductVal U)) t := by
  have heq : (fun s => smoothSpecialUnitaryProductDerivative n K b
        (smoothMatrixProductPositive a (p s)) (specialUnitaryProductVal U))
      =ᶠ[𝓝 t] (fun s => smoothSpecialUnitaryProductDerivative n K b (p s)
        (specialUnitaryProductVal U)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact smoothMatrixProductPositive_derivative_eq_on_group a ha (p s) (hp s hs.le)
      (specialUnitaryProductFrame b) (fun i => congrFun (specialUnitaryProductFrame_skew b) i)
      (specialUnitaryProductFrame_trace b) U
  have h := (htime t ht b U).congr_of_eventuallyEq heq
  have hLe := smoothMatrixProductDerivative_eq_on_group (specialUnitaryProductFrame b)
    (fun i => congrFun (specialUnitaryProductFrame_skew b) i)
    (specialUnitaryProductFrame_trace b)
    (derivationLaplacian (smoothSpecialUnitaryProductDerivative n K)
      (smoothMatrixProductPositive a (p t)))
    (derivationLaplacian (smoothSpecialUnitaryProductDerivative n K) (p t))
    (smoothMatrixProductPositive_laplacian_eq_on_group a ha (p t) (hp t ht.le)) U
  change HasDerivAt _ (smoothRightMatrixProductDerivative (specialUnitaryProductFrame b)
    (derivationLaplacian (smoothSpecialUnitaryProductDerivative n K)
      (smoothMatrixProductPositive a (p t))) (specialUnitaryProductVal U)) t
  rw [hLe]
  exact h

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ProductPolynomialHeatODE -/
section
open MeasureTheory Filter Set
open scoped Topology Matrix Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 800000

/-- Differentiating any tangent derivative of polynomial heat gives D Lp.
The proof differentiates a genuine finite-dimensional linear functional and
uses equality of smooth representatives on the group. -/
theorem specialUnitaryProductSmoothHeat_derivative_hasDerivAt {n K d : ℕ} [NeZero n]
    (f : specialUnitaryProductPolynomialHilbert n K d)
    (B : MatrixProduct n K) (hB : ∀ i, star (B i) = -B i) (htr : ∀ i, (B i).trace = 0)
    (t : ℝ) (U : SpecialUnitaryProduct n K) :
    HasDerivAt (fun s => smoothRightMatrixProductDerivative B
      (specialUnitaryProductSmoothHeat n K d f s) (specialUnitaryProductVal U))
      (smoothRightMatrixProductDerivative B
        (derivationLaplacian (smoothSpecialUnitaryProductDerivative n K)
          (specialUnitaryProductSmoothHeat n K d f t)) (specialUnitaryProductVal U)) t := by
  let Q : specialUnitaryProductPolynomialHilbert n K d →ₗ[ℝ] ℝ :=
    (smoothMatrixProductEvaluation (specialUnitaryProductVal U)).toLinearMap.comp
      ((smoothRightMatrixProductDerivative B).comp
        (specialUnitaryProductPolynomialSmoothLift n K d))
  have h := Q.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (specialUnitaryProductPolynomialHeat_hasDerivAt n K d f t)
  change HasDerivAt (fun s => smoothRightMatrixProductDerivative B
      (specialUnitaryProductSmoothHeat n K d f s) (specialUnitaryProductVal U))
    (smoothRightMatrixProductDerivative B
      (specialUnitaryProductPolynomialSmoothLift n K d
        (specialUnitaryProductPolynomialHilbertLaplacian n K d
          (specialUnitaryProductPolynomialHeat n K d t f))) (specialUnitaryProductVal U)) t at h
  have heq (V : SpecialUnitaryProduct n K) :
      specialUnitaryProductPolynomialSmoothLift n K d
        (specialUnitaryProductPolynomialHilbertLaplacian n K d
          (specialUnitaryProductPolynomialHeat n K d t f)) (specialUnitaryProductVal V) =
      derivationLaplacian (smoothSpecialUnitaryProductDerivative n K)
        (specialUnitaryProductSmoothHeat n K d f t) (specialUnitaryProductVal V) := by
    exact congrArg (fun g : C(SpecialUnitaryProduct n K, ℝ) => g V)
      ((specialUnitaryProductPolynomialSmoothLift_restrict
        (specialUnitaryProductPolynomialHilbertLaplacian n K d
          (specialUnitaryProductPolynomialHeat n K d t f))).trans
        (specialUnitaryProductPolynomialLaplacian_representative
          (specialUnitaryProductPolynomialHeat n K d t f)))
  have hd := smoothMatrixProductDerivative_eq_on_group B hB htr _ _ heq U
  rw [hd] at h
  exact h

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2FisherAlgebra -/
section
namespace BosonicLearn.Prop2
noncomputable section

variable {A ι : Type*} [CommRing A] [Algebra ℝ A] [Fintype ι]

theorem derivationGamma_symm (D : ι → A →ₗ[ℝ] A) (f g : A) :
    derivationGamma D f g = derivationGamma D g f := by
  simp only [derivationGamma, mul_comm]

theorem derivationGamma_add_right (D : ι → A →ₗ[ℝ] A) (f g h : A) :
    derivationGamma D f (g+h) = derivationGamma D f g + derivationGamma D f h := by
  simp [derivationGamma, mul_add, Finset.sum_add_distrib]

/-- An invariant integration functional gives integration by parts on its
smooth test-function algebra. -/
theorem derivation_integration_by_parts
    (D : ι → A →ₗ[ℝ] A) (m : A →ₗ[ℝ] ℝ)
    (hD : ∀ i f g, D i (f * g) = D i f * g + f * D i g)
    (hzero : ∀ i f, m (D i f) = 0)
    (i : ι) (f g : A) : m (f * D i g) = -m (D i f * g) := by
  have h := hzero i (f*g)
  rw [hD, map_add] at h
  linarith

theorem laplacian_integration_by_parts
    (D : ι → A →ₗ[ℝ] A) (m : A →ₗ[ℝ] ℝ)
    (hD : ∀ i f g, D i (f * g) = D i f * g + f * D i g)
    (hzero : ∀ i f, m (D i f) = 0)
    (f g : A) : m (f * derivationLaplacian D g) = -m (derivationGamma D f g) := by
  simp only [derivationLaplacian_apply, Finset.mul_sum, map_sum, derivationGamma]
  simp_rw [derivation_integration_by_parts D m hD hzero]
  simp only [Finset.sum_neg_distrib]

theorem laplacian_symmetric_integration
    (D : ι → A →ₗ[ℝ] A) (m : A →ₗ[ℝ] ℝ)
    (hD : ∀ i f g, D i (f * g) = D i f * g + f * D i g)
    (hzero : ∀ i f, m (D i f) = 0)
    (f g : A) : m (f * derivationLaplacian D g) = m (g * derivationLaplacian D f) := by
  rw [laplacian_integration_by_parts D m hD hzero,
    laplacian_integration_by_parts D m hD hzero, derivationGamma_symm D f g]

/-- Exponentiation's first-order chain rule determines the weighted carré du champ. -/
theorem derivationGamma_exp_left
    (D : ι → A →ₗ[ℝ] A) (g e h : A)
    (hexp : ∀ i, D i e = e * D i g) :
    derivationGamma D e h = e * derivationGamma D g h := by
  simp [derivationGamma, hexp, Finset.mul_sum, mul_assoc]

/-- The pointwise chain rule for the generator acting on exp(g). -/
theorem derivationLaplacian_exp
    (D : ι → A →ₗ[ℝ] A)
    (hD : ∀ i f g, D i (f * g) = D i f * g + f * D i g)
    (g e : A) (hexp : ∀ i, D i e = e * D i g) :
    derivationLaplacian D e =
      e * (derivationLaplacian D g + derivationGamma D g g) := by
  rw [derivationLaplacian_apply]
  simp_rw [hexp, hD, hexp]
  simp only [derivationLaplacian_apply, derivationGamma, mul_add,
    Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]
  ring

/-- The algebraic Fisher-information dissipation identity. Analytic
justification of differentiating a particular heat flow is kept separate. -/
theorem fisher_dissipation_algebra
    (D : ι → A →ₗ[ℝ] A) (m : A →ₗ[ℝ] ℝ)
    (hD : ∀ i f g, D i (f * g) = D i f * g + f * D i g)
    (hzero : ∀ i f, m (D i f) = 0)
    (g e : A) (hexp : ∀ i, D i e = e * D i g) :
    m (derivationLaplacian D e * derivationGamma D g g) +
      2 * m (e * derivationGamma D g
        (derivationLaplacian D g + derivationGamma D g g)) =
    -m (e * (derivationLaplacian D (derivationGamma D g g) -
      2 * derivationGamma D g (derivationLaplacian D g))) := by
  have h1 : m (derivationLaplacian D e * derivationGamma D g g) =
      m (e * derivationLaplacian D (derivationGamma D g g)) := by
    rw [mul_comm]
    exact laplacian_symmetric_integration D m hD hzero _ _
  have h2 : m (e * derivationGamma D g (derivationGamma D g g)) =
      -m (e * derivationLaplacian D (derivationGamma D g g)) := by
    rw [laplacian_integration_by_parts D m hD hzero,
      derivationGamma_exp_left D g e _ hexp, neg_neg]
  rw [h1, derivationGamma_add_right, mul_add, map_add, h2]
  rw [mul_sub, map_sub]
  have hscale (a : A) : m (2 * a) = 2 * m a := by
    simpa only [two_smul ℝ, two_mul] using m.map_smul (2 : ℝ) a
  rw [show e * (2 * derivationGamma D g (derivationLaplacian D g)) =
    2 * (e * derivationGamma D g (derivationLaplacian D g)) by ring, hscale]
  ring

/-- Integrating the pointwise curvature inequality against a positive density
controls the algebraic Fisher dissipation. Positivity of the integration
functional is stated on its concrete evaluation space. -/
theorem fisher_dissipation_le_of_curvature {Ω : Type*}
    (D : ι → A →ₗ[ℝ] A) (m : A →ₗ[ℝ] ℝ) (ev : Ω → A →ₐ[ℝ] ℝ)
    (hD : ∀ i f g, D i (f * g) = D i f * g + f * D i g)
    (hzero : ∀ i f, m (D i f) = 0)
    (hpositive : ∀ a : A, (∀ x, 0 ≤ ev x a) → 0 ≤ m a)
    (κ : ℝ) (g e : A) (hexp : ∀ i, D i e = e * D i g)
    (he : ∀ x, 0 ≤ ev x e)
    (hcurv : ∀ x, κ * ev x (derivationGamma D g g) ≤
      (ev x (derivationLaplacian D (derivationGamma D g g)) -
        2 * ev x (derivationGamma D g (derivationLaplacian D g))) / 2) :
    m (derivationLaplacian D e * derivationGamma D g g) +
      2 * m (e * derivationGamma D g
        (derivationLaplacian D g + derivationGamma D g g)) ≤
      -(2 * κ) * m (e * derivationGamma D g g) := by
  rw [fisher_dissipation_algebra D m hD hzero g e hexp]
  have h := hpositive
    (e * (derivationLaplacian D (derivationGamma D g g) -
      2 * derivationGamma D g (derivationLaplacian D g)) -
        (2 * κ) • (e * derivationGamma D g g)) (by
    intro x
    simp only [map_sub, map_mul, map_ofNat, map_smul, smul_eq_mul]
    have hc := mul_le_mul_of_nonneg_left (hcurv x) (he x)
    nlinarith)
  simp only [map_sub, map_smul, smul_eq_mul] at h
  linarith

/-- Pointwise logarithmic heat velocity, derived from the genuine exponential
chain rule rather than assumed as a differential identity. -/
theorem logarithmic_velocity_apply
    (D : ι → A →ₗ[ℝ] A)
    (hD : ∀ i f g, D i (f * g) = D i f * g + f * D i g)
    (g e : A) (hexp : ∀ i, D i e = e * D i g)
    (ev : A →ₐ[ℝ] ℝ) (he : ev e ≠ 0) :
    ev (derivationLaplacian D g + derivationGamma D g g) =
      ev (derivationLaplacian D e) / ev e := by
  have h := congrArg ev (derivationLaplacian_exp D hD g e hexp)
  rw [map_mul] at h
  apply (eq_div_iff he).mpr
  rw [h]
  ring

/-- Its invariant spatial derivative in quotient form, used when differentiating
Fisher information along a finite-dimensional heat trajectory. -/
theorem logarithmic_velocity_derivative_apply
    (D : ι → A →ₗ[ℝ] A)
    (hD : ∀ i f g, D i (f * g) = D i f * g + f * D i g)
    (g e : A) (hexp : ∀ i, D i e = e * D i g)
    (ev : A →ₐ[ℝ] ℝ) (he : ev e ≠ 0) (i : ι) :
    ev (D i (derivationLaplacian D g + derivationGamma D g g)) =
      (ev (D i (derivationLaplacian D e)) * ev e -
        ev (derivationLaplacian D e) * ev (D i e)) / (ev e)^2 := by
  have h := congrArg (fun f => ev (D i f)) (derivationLaplacian_exp D hD g e hexp)
  rw [hD, map_add, map_mul, map_mul] at h
  rw [logarithmic_velocity_apply D hD g e hexp ev he] at h
  field_simp
  field_simp at h
  nlinarith

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2HeatPointwise -/
section
namespace BosonicLearn.Prop2
noncomputable section

variable {A ι : Type*} [CommRing A] [Algebra ℝ A] [Fintype ι]

/-- A first invariant derivative of log-density satisfies the differentiated
heat equation. Time differentiation is only required for the density and its
first invariant derivatives, as supplied by a finite-dimensional linear ODE. -/
theorem hasDerivAt_invariant_log_heat
    (D : ι → A →ₗ[ℝ] A)
    (hD : ∀ i f g, D i (f*g) = D i f*g + f*D i g)
    (e g : ℝ → A) (ev : A →ₐ[ℝ] ℝ)
    (he : ∀ s, ev (e s) ≠ 0) (hexp : ∀ s i, D i (e s) = e s * D i (g s))
    (t : ℝ) (i : ι)
    (ht : HasDerivAt (fun s => ev (e s)) (ev (derivationLaplacian D (e t))) t)
    (hti : HasDerivAt (fun s => ev (D i (e s))) (ev (D i (derivationLaplacian D (e t)))) t) :
    HasDerivAt (fun s => ev (D i (g s)))
      (ev (D i (derivationLaplacian D (g t) + derivationGamma D (g t) (g t)))) t := by
  have hquot : (fun s => ev (D i (g s))) = fun s => ev (D i (e s)) / ev (e s) := by
    funext s
    apply (eq_div_iff (he s)).mpr
    have h := congrArg ev (hexp s i)
    rw [map_mul] at h
    rw [h]
    ring
  rw [hquot, logarithmic_velocity_derivative_apply D hD (g t) (e t) (hexp t) ev (he t)]
  simpa only [mul_comm] using hti.fun_div ht (he t)

/-- The genuine pointwise time derivative of Fisher information's density. -/
theorem hasDerivAt_fisher_density
    (D : ι → A →ₗ[ℝ] A)
    (hD : ∀ i f g, D i (f*g) = D i f*g + f*D i g)
    (e g : ℝ → A) (ev : A →ₐ[ℝ] ℝ)
    (he : ∀ s, ev (e s) ≠ 0) (hexp : ∀ s i, D i (e s) = e s * D i (g s))
    (t : ℝ)
    (ht : HasDerivAt (fun s => ev (e s)) (ev (derivationLaplacian D (e t))) t)
    (hti : ∀ i, HasDerivAt (fun s => ev (D i (e s)))
      (ev (D i (derivationLaplacian D (e t)))) t) :
    HasDerivAt (fun s => ev (e s * derivationGamma D (g s) (g s)))
      (ev (derivationLaplacian D (e t) * derivationGamma D (g t) (g t)) +
        2 * ev (e t * derivationGamma D (g t)
          (derivationLaplacian D (g t) + derivationGamma D (g t) (g t)))) t := by
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (hasDerivAt_invariant_log_heat D hD e g ev he hexp t i ht (hti i)).fun_mul
      (hasDerivAt_invariant_log_heat D hD e g ev he hexp t i ht (hti i)))
  have hmul := ht.fun_mul hsum
  simp only [derivationGamma, map_sum, map_mul] at *
  convert hmul using 1 <;> try rfl
  simp only [Finset.sum_add_distrib]
  simp_rw [mul_comm]
  ring

/-- The pointwise entropy-density derivative under the heat equation. -/
theorem hasDerivAt_entropy_density
    (e g : ℝ → A) (ev : A →ₐ[ℝ] ℝ) (t v : ℝ)
    (he : ∀ s, ev (e s) ≠ 0)
    (hg : ∀ s, ev (g s) = Real.log (ev (e s)))
    (ht : HasDerivAt (fun s => ev (e s)) v t) :
    HasDerivAt (fun s => ev (e s * g s)) (v * (ev (g t) + 1)) t := by
  have hlog := ht.log (he t)
  have heq : (fun s => ev (g s)) = fun s => Real.log (ev (e s)) := funext hg
  rw [← heq] at hlog
  have h := ht.fun_mul hlog
  simp only [map_mul]
  have hv : v * (ev (g t) + 1) = v * ev (g t) + ev (e t) * (v / ev (e t)) := by
    field_simp [he t]
  rw [hv]
  exact h

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2CompactDifferentiation -/
section
open MeasureTheory Set Filter
open scoped Topology

namespace BosonicLearn.Prop2
noncomputable section

/-- Continuous parameter derivatives pass through finite integration on a
compact space. The derivative hypothesis is needed only in a neighborhood of
the chosen parameter, permitting heat flows defined for nonnegative times. -/
theorem hasDerivAt_integral_compact
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (F F' : ℝ → X → ℝ) (t : ℝ)
    (hF : Continuous (Function.uncurry F)) (hF' : Continuous (Function.uncurry F'))
    (hderiv : ∀ᶠ s in 𝓝 t, ∀ x, HasDerivAt (fun r => F r x) (F' s x) s) :
    HasDerivAt (fun s => ∫ x, F s x ∂μ) (∫ x, F' t x ∂μ) t := by
  obtain ⟨ε, hε, hεderiv⟩ := Metric.eventually_nhds_iff.mp hderiv
  let δ := min (ε/2) 1
  have hδ : 0 < δ := lt_min (by positivity) zero_lt_one
  have hc : IsCompact ((Icc (t-δ) (t+δ)) ×ˢ (univ : Set X)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := hc.bddAbove_image hF'.norm.continuousOn
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (x₀ := t) (s := Icc (t-δ) (t+δ))
    (bound := fun _ => C)
    (Icc_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall (fun s =>
      (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable))
    ((hF.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (by simp)))
    ((hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x s hs => hC (mem_image_of_mem
      (fun p : ℝ × X => ‖F' p.1 p.2‖)
      (show (s,x) ∈ (Icc (t-δ) (t+δ)) ×ˢ (univ : Set X) from ⟨hs, mem_univ x⟩))))
    (integrable_const C)
    (Filter.Eventually.of_forall (fun x s hs => hεderiv (by
      rw [Real.dist_eq, abs_lt]
      have hd : δ ≤ ε/2 := min_le_left _ _
      constructor <;> linarith [hs.1, hs.2]) x))
  exact hi.2

/-- Joint continuity implies continuity of compact-space expectations. -/
theorem continuous_integral_compact
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (F : ℝ → X → ℝ) (hF : Continuous (Function.uncurry F)) :
    Continuous (fun t => ∫ x, F t x ∂μ) := by
  simpa only [Measure.restrict_univ] using
    continuous_parametric_integral_of_continuous (μ := μ) hF (isCompact_univ : IsCompact (univ : Set X))

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2Herbst -/
section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace BosonicLearn.Prop5

/-- The scalar differential inequality at the heart of the Herbst argument. -/
theorem herbst_differential_bound (ψ : ℝ → ℝ) (hψ : Differentiable ℝ ψ)
    (hzero : ψ 0 = 0) (C : ℝ)
    (hent : ∀ t : ℝ, 0 < t → t * deriv ψ t - ψ t ≤ C * t^2)
    (t : ℝ) (ht : 0 < t) :
    ψ t ≤ deriv ψ 0 * t + C * t^2 := by
  let q : ℝ → ℝ := fun x => ψ x / x - C * x
  have hdq (x : ℝ) (hx : 0 < x) :
      HasDerivAt q ((deriv ψ x * x - ψ x) / x^2 - C) x := by
    simpa only [q, mul_one, id_eq] using ((hψ x).hasDerivAt.fun_div (hasDerivAt_id x) hx.ne').fun_sub
      ((hasDerivAt_id x).const_mul C)
  have hanti : AntitoneOn q (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · intro x hx
      exact (hdq x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hdq x (by simpa only [interior_Ioi, Set.mem_Ioi] using hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hxpos : 0 < x := by simpa only [interior_Ioi, Set.mem_Ioi] using hx
      rw [(hdq x hxpos).deriv]
      apply sub_nonpos.mpr
      apply (div_le_iff₀ (sq_pos_of_pos hxpos)).mpr
      simpa only [mul_comm (deriv ψ x) x] using hent x hxpos
  have hlim : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 (deriv ψ 0)) := by
    have hslope := (hψ 0).hasDerivAt.tendsto_slope_zero_right
    have hid : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := nhdsWithin_le_nhds
    have h := hslope.sub (hid.const_mul C)
    simpa [q, hzero, smul_eq_mul, div_eq_mul_inv, mul_comm] using h
  have hle : q t ≤ deriv ψ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds] with x hx hxt
    exact hanti hx ht hxt.le
  have hm := mul_le_mul_of_nonneg_right hle ht.le
  dsimp only [q] at hm
  rw [sub_mul, div_mul_cancel₀ _ ht.ne'] at hm
  nlinarith

/-- Exponential-entropy control implies a lower bound for the mean relative to
the log of the exponential mean. This is the probabilistic Herbst argument. -/
theorem logmean_le_mean_add_of_entropy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ) (C : ℝ)
    (hint : ∀ t : ℝ, Integrable (fun x => Real.exp (t * F x)) μ)
    (hent : ∀ t : ℝ, 0 < t →
      (∫ x, t * F x * Real.exp (t * F x) ∂μ) -
        (∫ x, Real.exp (t * F x) ∂μ) * Real.log (∫ x, Real.exp (t * F x) ∂μ) ≤
          C * t^2 * ∫ x, Real.exp (t * F x) ∂μ) :
    Real.log (∫ x, Real.exp (F x) ∂μ) ≤ (∫ x, F x ∂μ) + C := by
  have hexpset : integrableExpSet F μ = Set.univ := by
    ext t
    simp only [Set.mem_univ, iff_true]
    exact hint t
  have hinterior (t : ℝ) : t ∈ interior (integrableExpSet F μ) := by simp [hexpset]
  have hdiff : Differentiable ℝ (cgf F μ) :=
    fun t => (analyticAt_cgf (hinterior t)).differentiableAt
  have hineq (t : ℝ) (ht : 0 < t) :
      t * deriv (cgf F μ) t - cgf F μ t ≤ C * t^2 := by
    rw [deriv_cgf (hinterior t)]
    have hm : 0 < mgf F μ t := mgf_pos (hint t)
    have heq : t * ((∫ x, F x * Real.exp (t * F x) ∂μ) / mgf F μ t) - cgf F μ t =
        ((∫ x, t * F x * Real.exp (t * F x) ∂μ) -
          mgf F μ t * Real.log (mgf F μ t)) / mgf F μ t := by
      simp_rw [mul_assoc t (F _)]
      rw [integral_const_mul]
      unfold cgf
      field_simp
    rw [heq]
    apply (div_le_iff₀ hm).mpr
    exact hent t ht
  have h := herbst_differential_bound (cgf F μ) hdiff (cgf_zero) C hineq 1 (by norm_num)
  rw [deriv_cgf_zero (hinterior 0)] at h
  simpa [cgf, mgf] using h

/-- If the exponential mean is at least one, the entropy constant controls the
possible negative mean. -/
theorem mean_ge_neg_of_exp_mean_ge_one_entropy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ) (C : ℝ)
    (hint : ∀ t : ℝ, Integrable (fun x => Real.exp (t * F x)) μ)
    (hent : ∀ t : ℝ, 0 < t →
      (∫ x, t * F x * Real.exp (t * F x) ∂μ) -
        (∫ x, Real.exp (t * F x) ∂μ) * Real.log (∫ x, Real.exp (t * F x) ∂μ) ≤
          C * t^2 * ∫ x, Real.exp (t * F x) ∂μ)
    (hmean : 1 ≤ ∫ x, Real.exp (F x) ∂μ) :
    -C ≤ ∫ x, F x ∂μ := by
  have h := logmean_le_mean_add_of_entropy μ F C hint hent
  have hlog := Real.log_nonneg hmean
  linarith

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop2EntropyFlow -/
section
open MeasureTheory Filter
open scoped Topology

namespace BosonicLearn.Prop2
noncomputable section

/-- Integrating exponential entropy dissipation, without assuming the desired
logarithmic Sobolev conclusion. The hypotheses are the three analytic facts
supplied by a heat-flow proof: differentiation, gradient decay, and convergence. -/
theorem entropy_bound_of_dissipation_decay
    (E I : ℝ → ℝ) (κ A : ℝ) (hκ : 0 < κ)
    (hE : ContinuousOn E (Set.Ici 0))
    (hderiv : ∀ t : ℝ, 0 < t → HasDerivAt E (-I t) t)
    (hdecay : ∀ t : ℝ, 0 < t → I t ≤ A * Real.exp (-(2 * κ) * t))
    (hlim : Tendsto E atTop (𝓝 0)) :
    E 0 ≤ A / (2 * κ) := by
  let g : ℝ → ℝ := fun t => E t - A / (2 * κ) * Real.exp (-(2 * κ) * t)
  have hg : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact hE.sub (by fun_prop)
    · intro t ht
      have ht0 : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
      exact ((hderiv t ht0).fun_sub
        ((((hasDerivAt_id t).const_mul (-(2 * κ))).exp).const_mul
          (A / (2 * κ)))).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht0 : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
      have hd := (hderiv t ht0).fun_sub
        ((((hasDerivAt_id t).const_mul (-(2 * κ))).exp).const_mul (A / (2 * κ)))
      change 0 ≤ deriv g t
      have hdg : HasDerivAt g
          (-I t - A / (2 * κ) * (Real.exp (-(2 * κ) * t) * (-(2 * κ) * 1))) t := by
        simpa only [g, id_eq, Pi.sub_apply] using hd
      rw [hdg.deriv]
      have heq : A / (2 * κ) * (Real.exp (-(2 * κ) * t) * (-(2 * κ) * 1)) =
          -(A * Real.exp (-(2 * κ) * t)) := by field_simp
      rw [heq]
      linarith [hdecay t ht0]
  have he : Tendsto (fun t : ℝ => Real.exp (-(2 * κ) * t)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact Tendsto.const_mul_atTop_of_neg (by linarith : -(2 * κ) < 0) tendsto_id
  have hglim : Tendsto g atTop (𝓝 0) := by
    simpa [g] using hlim.sub (he.const_mul (A / (2 * κ)))
  have hle : g 0 ≤ 0 := by
    apply ge_of_tendsto hglim
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hg (by simp) ht ht
  simpa [g] using hle

/-- The integrating-factor form of the Fisher-information decay estimate. -/
theorem fisher_decay_of_differential
    (I I' : ℝ → ℝ) (κ : ℝ)
    (hI : ContinuousOn I (Set.Ici 0))
    (hderiv : ∀ t : ℝ, 0 < t → HasDerivAt I (I' t) t)
    (hbound : ∀ t : ℝ, 0 < t → I' t ≤ -(2 * κ) * I t)
    (t : ℝ) (ht : 0 ≤ t) :
    I t ≤ I 0 * Real.exp (-(2 * κ) * t) := by
  let g : ℝ → ℝ := fun s => Real.exp ((2 * κ) * s) * I s
  have hg : AntitoneOn g (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact (by fun_prop : ContinuousOn (fun s : ℝ => Real.exp ((2 * κ) * s)) (Set.Ici 0)).mul hI
    · intro s hs
      have hs0 : 0 < s := by simpa only [interior_Ici, Set.mem_Ioi] using hs
      exact (((((hasDerivAt_id s).const_mul (2 * κ)).exp).fun_mul
        (hderiv s hs0))).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs0 : 0 < s := by simpa only [interior_Ici, Set.mem_Ioi] using hs
      have hd := (((hasDerivAt_id s).const_mul (2 * κ)).exp).fun_mul (hderiv s hs0)
      have hdg : HasDerivAt g
          (Real.exp ((2 * κ) * s) * (2 * κ * 1) * I s +
            Real.exp ((2 * κ) * s) * I' s) s := by
        simpa only [g, id_eq] using hd
      rw [hdg.deriv]
      have hm := mul_le_mul_of_nonneg_left (hbound s hs0) (Real.exp_pos ((2 * κ) * s)).le
      nlinarith
  have h := hg (by simp) ht ht
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(2 * κ) * t)).le
  dsimp only [g] at hm
  simp only [mul_zero, Real.exp_zero, one_mul] at hm
  have he : Real.exp (-(2 * κ) * t) * Real.exp ((2 * κ) * t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  rw [← mul_assoc, he, one_mul] at hm
  simpa only [mul_comm] using hm

/-- The two scalar heat-flow differential identities yield logarithmic Sobolev
control once convergence to equilibrium is supplied. -/
theorem entropy_bound_of_fisher_differential
    (E I I' : ℝ → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hE : ContinuousOn E (Set.Ici 0)) (hI : ContinuousOn I (Set.Ici 0))
    (hderivE : ∀ t : ℝ, 0 < t → HasDerivAt E (-I t) t)
    (hderivI : ∀ t : ℝ, 0 < t → HasDerivAt I (I' t) t)
    (hbound : ∀ t : ℝ, 0 < t → I' t ≤ -(2 * κ) * I t)
    (hlim : Tendsto E atTop (𝓝 0)) :
    E 0 ≤ I 0 / (2 * κ) := by
  exact entropy_bound_of_dissipation_decay E I κ (I 0) hκ hE hderivE
    (fun t ht => fisher_decay_of_differential I I' κ hI hderivI hbound t ht.le) hlim

/-- A dimension-scaled entropy-flow estimate feeds the already proved Herbst
argument. No group-specific heat-flow assertion is assumed implicitly. -/
theorem logmean_bound_of_entropy_flow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ)
    (κ L : ℝ) (hκ : 0 < κ)
    (hint : ∀ t : ℝ, Integrable (fun x => Real.exp (t * F x)) μ)
    (E I : ℝ → ℝ → ℝ)
    (hE : ∀ s : ℝ, 0 < s → ContinuousOn (E s) (Set.Ici 0))
    (hzero : ∀ s : ℝ, 0 < s → E s 0 =
      (∫ x, s * F x * Real.exp (s * F x) ∂μ) -
        (∫ x, Real.exp (s * F x) ∂μ) * Real.log (∫ x, Real.exp (s * F x) ∂μ))
    (hderiv : ∀ s : ℝ, 0 < s → ∀ t : ℝ, 0 < t → HasDerivAt (E s) (-I s t) t)
    (hdecay : ∀ s : ℝ, 0 < s → ∀ t : ℝ, 0 < t →
      I s t ≤ (L^2 * s^2 * ∫ x, Real.exp (s * F x) ∂μ) * Real.exp (-(2 * κ) * t))
    (hlim : ∀ s : ℝ, 0 < s → Tendsto (E s) atTop (𝓝 0)) :
    Real.log (∫ x, Real.exp (F x) ∂μ) ≤ (∫ x, F x ∂μ) + L^2 / (2 * κ) := by
  apply Prop5.logmean_le_mean_add_of_entropy μ F (L^2 / (2 * κ)) hint
  intro s hs
  have h := entropy_bound_of_dissipation_decay (E s) (I s) κ
    (L^2 * s^2 * ∫ x, Real.exp (s * F x) ∂μ) hκ (hE s hs)
      (hderiv s hs) (hdecay s hs) (hlim s hs)
  rw [hzero s hs] at h
  convert h using 1 <;> ring

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2HeatInformation -/
section
open MeasureTheory Set Filter
open scoped Topology

namespace BosonicLearn.Prop2
noncomputable section

variable {A ι X : Type*} [CommRing A] [Algebra ℝ A] [Fintype ι]
  [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Entropy differentiation along a genuine heat trajectory, with compactness
providing the domination needed to differentiate the integral. -/
theorem heat_entropy_hasDerivAt
    (μ : Measure X) [IsFiniteMeasure μ] (ev : X → A →ₐ[ℝ] ℝ)
    (m : A →ₗ[ℝ] ℝ) (hm : ∀ f, m f = ∫ x, ev x f ∂μ)
    (D : ι → A →ₗ[ℝ] A)
    (hD : ∀ i f g, D i (f*g) = D i f*g + f*D i g)
    (hzero : ∀ i f, m (D i f) = 0)
    (e g : ℝ → A) (he : ∀ s x, ev x (e s) ≠ 0)
    (hg : ∀ s x, ev x (g s) = Real.log (ev x (e s)))
    (hexp : ∀ s i, D i (e s) = e s * D i (g s))
    (hce : Continuous (fun p : ℝ × X => ev p.2 (e p.1)))
    (hcg : Continuous (fun p : ℝ × X => ev p.2 (g p.1)))
    (hcLe : Continuous (fun p : ℝ × X => ev p.2 (derivationLaplacian D (e p.1))))
    (htime : ∀ t : ℝ, 0 < t → ∀ x,
      HasDerivAt (fun s => ev x (e s)) (ev x (derivationLaplacian D (e t))) t)
    (t : ℝ) (ht : 0 < t) (c : ℝ) :
    HasDerivAt (fun s => m (e s * g s) - c)
      (-m (e t * derivationGamma D (g t) (g t))) t := by
  have h := hasDerivAt_integral_compact μ
    (fun s x => ev x (e s * g s))
    (fun s x => ev x (derivationLaplacian D (e s)) * (ev x (g s) + 1)) t
    (by simpa only [Function.uncurry_apply_pair, map_mul, Pi.mul_apply] using! hce.mul hcg)
    (hcLe.mul (hcg.add continuous_const)) (by
      filter_upwards [eventually_gt_nhds ht] with s hs
      intro x
      exact hasDerivAt_entropy_density e g (ev x) s _ (fun r => he r x)
        (fun r => hg r x) (htime s hs x))
  have hF : (fun s => ∫ x, ev x (e s * g s) ∂μ) = fun s => m (e s*g s) := by
    funext s
    exact (hm _).symm
  rw [hF] at h
  have hval : (∫ x, ev x (derivationLaplacian D (e t)) * (ev x (g t) + 1) ∂μ) =
      -m (e t * derivationGamma D (g t) (g t)) := by
    have hz : m (derivationLaplacian D (e t)) = 0 := by
      simp only [derivationLaplacian_apply, map_sum, hzero, Finset.sum_const_zero]
    have hb := laplacian_integration_by_parts D m hD hzero (g t) (e t)
    rw [derivationGamma_symm D (g t) (e t),
      derivationGamma_exp_left D (g t) (e t) (g t) (hexp t)] at hb
    have hh : (∫ x, ev x (derivationLaplacian D (e t)) * (ev x (g t) + 1) ∂μ) =
        m (g t * derivationLaplacian D (e t) + derivationLaplacian D (e t)) := by
      rw [hm]
      congr 1
      funext x
      simp only [map_add, map_mul]
      ring
    rw [hh, map_add, hz, add_zero, hb]
  rw [hval] at h
  exact h.sub_const c

/-- Fisher information differentiation. The compact-space hypotheses are
ordinary joint continuity, and the only time-ODE inputs concern a finite family
of invariant derivatives of the density. -/
theorem heat_fisher_hasDerivAt
    (μ : Measure X) [IsFiniteMeasure μ] (ev : X → A →ₐ[ℝ] ℝ)
    (m : A →ₗ[ℝ] ℝ) (hm : ∀ f, m f = ∫ x, ev x f ∂μ)
    (D : ι → A →ₗ[ℝ] A)
    (hD : ∀ i f g, D i (f*g) = D i f*g + f*D i g)
    (e g : ℝ → A) (he : ∀ s x, ev x (e s) ≠ 0)
    (hexp : ∀ s i, D i (e s) = e s * D i (g s))
    (hcF : Continuous (fun p : ℝ × X =>
      ev p.2 (e p.1 * derivationGamma D (g p.1) (g p.1))))
    (hcF' : Continuous (fun p : ℝ × X =>
      ev p.2 (derivationLaplacian D (e p.1) * derivationGamma D (g p.1) (g p.1)) +
        2 * ev p.2 (e p.1 * derivationGamma D (g p.1)
          (derivationLaplacian D (g p.1) + derivationGamma D (g p.1) (g p.1)))))
    (htime : ∀ t : ℝ, 0 < t → ∀ x,
      HasDerivAt (fun s => ev x (e s)) (ev x (derivationLaplacian D (e t))) t)
    (hDtime : ∀ t : ℝ, 0 < t → ∀ i x,
      HasDerivAt (fun s => ev x (D i (e s))) (ev x (D i (derivationLaplacian D (e t)))) t)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => m (e s * derivationGamma D (g s) (g s)))
      (m (derivationLaplacian D (e t) * derivationGamma D (g t) (g t)) +
        2 * m (e t * derivationGamma D (g t)
          (derivationLaplacian D (g t) + derivationGamma D (g t) (g t)))) t := by
  have h := hasDerivAt_integral_compact μ
    (fun s x => ev x (e s * derivationGamma D (g s) (g s)))
    (fun s x => ev x (derivationLaplacian D (e s) * derivationGamma D (g s) (g s)) +
      2 * ev x (e s * derivationGamma D (g s)
        (derivationLaplacian D (g s) + derivationGamma D (g s) (g s)))) t
    (by simpa only [Function.uncurry_apply_pair] using! hcF)
    (by simpa only [Function.uncurry_apply_pair] using! hcF') (by
    filter_upwards [eventually_gt_nhds ht] with s hs
    intro x
    exact hasDerivAt_fisher_density D hD e g (ev x) (fun r => he r x) hexp s
      (htime s hs x) (fun i => hDtime s hs i x))
  have hF : (fun s => ∫ x, ev x (e s * derivationGamma D (g s) (g s)) ∂μ) =
      fun s => m (e s * derivationGamma D (g s) (g s)) := by
    funext s
    exact (hm _).symm
  rw [hF] at h
  have hval : (∫ x, ev x (derivationLaplacian D (e t) * derivationGamma D (g t) (g t)) +
      2 * ev x (e t * derivationGamma D (g t)
        (derivationLaplacian D (g t) + derivationGamma D (g t) (g t))) ∂μ) =
      m (derivationLaplacian D (e t) * derivationGamma D (g t) (g t)) +
        2 * m (e t * derivationGamma D (g t)
          (derivationLaplacian D (g t) + derivationGamma D (g t) (g t))) := by
    have hm2 (f : A) : m ((2:ℝ) • f) = 2 * m f := by
      simpa only [smul_eq_mul] using m.map_smul (2:ℝ) f
    rw [← hm2, ← map_add, hm]
    congr 1
    funext x
    simp only [map_add, map_smul, smul_eq_mul]
  rwa [hval] at h

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2HeatLogSobolev -/
section
open MeasureTheory Set Filter
open scoped Topology

namespace BosonicLearn.Prop2
noncomputable section

/-- Logarithmic Sobolev follows from an actual positive heat trajectory with
finite derivative ODEs, curvature, and convergence. All entropy and Fisher
identities are proved here; they are not assumptions of this interface. -/
theorem logSobolev_of_positive_heat
    {A ι X : Type*} [CommRing A] [Algebra ℝ A] [Fintype ι]
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (ev : X → A →ₐ[ℝ] ℝ)
    (m : A →ₗ[ℝ] ℝ) (hm : ∀ f, m f = ∫ x, ev x f ∂μ)
    (D : ι → A →ₗ[ℝ] A)
    (hD : ∀ i f g, D i (f*g) = D i f*g + f*D i g)
    (hzero : ∀ i f, m (D i f) = 0)
    (hpositive : ∀ f : A, (∀ x, 0 ≤ ev x f) → 0 ≤ m f)
    (κ : ℝ) (hκ : 0 < κ)
    (hcurv : ∀ f x, κ * ev x (derivationGamma D f f) ≤
      (ev x (derivationLaplacian D (derivationGamma D f f)) -
        2 * ev x (derivationGamma D f (derivationLaplacian D f))) / 2)
    (e g : ℝ → A) (he : ∀ s x, 0 < ev x (e s))
    (hg : ∀ s x, ev x (g s) = Real.log (ev x (e s)))
    (hexp : ∀ s i, D i (e s) = e s * D i (g s))
    (hce : Continuous (fun p : ℝ × X => ev p.2 (e p.1)))
    (hcg : Continuous (fun p : ℝ × X => ev p.2 (g p.1)))
    (hcLe : Continuous (fun p : ℝ × X => ev p.2 (derivationLaplacian D (e p.1))))
    (hcF : Continuous (fun p : ℝ × X =>
      ev p.2 (e p.1 * derivationGamma D (g p.1) (g p.1))))
    (hcF' : Continuous (fun p : ℝ × X =>
      ev p.2 (derivationLaplacian D (e p.1) * derivationGamma D (g p.1) (g p.1)) +
        2 * ev p.2 (e p.1 * derivationGamma D (g p.1)
          (derivationLaplacian D (g p.1) + derivationGamma D (g p.1) (g p.1)))))
    (htime : ∀ t : ℝ, 0 < t → ∀ x,
      HasDerivAt (fun s => ev x (e s)) (ev x (derivationLaplacian D (e t))) t)
    (hDtime : ∀ t : ℝ, 0 < t → ∀ i x,
      HasDerivAt (fun s => ev x (D i (e s))) (ev x (D i (derivationLaplacian D (e t)))) t)
    (hlim : Tendsto (fun t => m (e t * g t) - m (e 0) * Real.log (m (e 0))) atTop (𝓝 0)) :
    m (e 0 * g 0) - m (e 0) * Real.log (m (e 0)) ≤
      m (e 0 * derivationGamma D (g 0) (g 0)) / (2*κ) := by
  let E : ℝ → ℝ := fun t => m (e t * g t) - m (e 0) * Real.log (m (e 0))
  let I : ℝ → ℝ := fun t => m (e t * derivationGamma D (g t) (g t))
  let I' : ℝ → ℝ := fun t =>
    m (derivationLaplacian D (e t) * derivationGamma D (g t) (g t)) +
      2 * m (e t * derivationGamma D (g t)
        (derivationLaplacian D (g t) + derivationGamma D (g t) (g t)))
  have hcE : Continuous E := by
    have h := continuous_integral_compact μ (fun t x => ev x (e t*g t))
      (by simpa only [Function.uncurry_apply_pair, map_mul, Pi.mul_apply] using! hce.mul hcg)
    have hh : (fun t => ∫ x, ev x (e t*g t) ∂μ) = fun t => m (e t*g t) := by
      funext t
      exact (hm _).symm
    rw [hh] at h
    exact h.sub continuous_const
  have hcI : Continuous I := by
    have h := continuous_integral_compact μ
      (fun t x => ev x (e t * derivationGamma D (g t) (g t)))
      (by simpa only [Function.uncurry_apply_pair] using! hcF)
    have hh : (fun t => ∫ x, ev x (e t * derivationGamma D (g t) (g t)) ∂μ) = I := by
      funext t
      exact (hm _).symm
    rwa [hh] at h
  exact entropy_bound_of_fisher_differential E I I' κ hκ hcE.continuousOn hcI.continuousOn
    (fun t ht => heat_entropy_hasDerivAt μ ev m hm D hD hzero e g
      (fun s x => (he s x).ne') hg hexp hce hcg hcLe htime t ht _)
    (fun t ht => heat_fisher_hasDerivAt μ ev m hm D hD e g
      (fun s x => (he s x).ne') hexp hcF hcF' htime hDtime t ht)
    (fun t _ => fisher_dissipation_le_of_curvature D m ev hD hzero hpositive κ
      (g t) (e t) (hexp t) (fun x => (he t x).le) (hcurv (g t))) hlim

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ProductClampedLSI -/
section
open MeasureTheory Filter Set
open scoped Topology Matrix Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 1000000

/-- Apply actual product curvature and Haar integration to a positive heat
trajectory. The supplied ODEs are those of its unmodified polynomial lift;
clamping is proved to preserve them on the group. -/
theorem product_logSobolev_of_clamped_heat {n K : ℕ} [NeZero n]
    (p : ℝ → smoothMatrixProductFunctions n K) (a : ℝ) (ha : 0 < a)
    (hp : ∀ s : ℝ, 0 ≤ s → ∀ U : SpecialUnitaryProduct n K,
      2*a ≤ p s (specialUnitaryProductVal U))
    (htime : ∀ t : ℝ, 0 < t → ∀ U : SpecialUnitaryProduct n K,
      HasDerivAt (fun s => p s (specialUnitaryProductVal U))
        (derivationLaplacian (smoothSpecialUnitaryProductDerivative n K) (p t)
          (specialUnitaryProductVal U)) t)
    (hDtime : ∀ t : ℝ, 0 < t → ∀ b : SpecialUnitaryProductFrameIndex n K,
      ∀ U : SpecialUnitaryProduct n K,
      HasDerivAt (fun s => smoothSpecialUnitaryProductDerivative n K b (p s)
          (specialUnitaryProductVal U))
        (smoothSpecialUnitaryProductDerivative n K b
          (derivationLaplacian (smoothSpecialUnitaryProductDerivative n K) (p t))
          (specialUnitaryProductVal U)) t)
    (hcont :
      let e := fun s => smoothMatrixProductPositive a (p s)
      let g := fun s => smoothMatrixProductLog (e s) (smoothMatrixProductPositive_ne_zero a ha (p s))
      let D := smoothSpecialUnitaryProductDerivative n K
      Continuous (fun z : ℝ × SpecialUnitaryProduct n K => e z.1 (specialUnitaryProductVal z.2)) ∧
      Continuous (fun z : ℝ × SpecialUnitaryProduct n K => g z.1 (specialUnitaryProductVal z.2)) ∧
      Continuous (fun z : ℝ × SpecialUnitaryProduct n K =>
        derivationLaplacian D (e z.1) (specialUnitaryProductVal z.2)) ∧
      Continuous (fun z : ℝ × SpecialUnitaryProduct n K =>
        (e z.1 * derivationGamma D (g z.1) (g z.1)) (specialUnitaryProductVal z.2)) ∧
      Continuous (fun z : ℝ × SpecialUnitaryProduct n K =>
        (derivationLaplacian D (e z.1) * derivationGamma D (g z.1) (g z.1)) (specialUnitaryProductVal z.2) +
        2 * (e z.1 * derivationGamma D (g z.1)
          (derivationLaplacian D (g z.1) + derivationGamma D (g z.1) (g z.1))) (specialUnitaryProductVal z.2)))
    (hlim :
      let e := fun s => smoothMatrixProductPositive a (p s)
      let g := fun s => smoothMatrixProductLog (e s) (smoothMatrixProductPositive_ne_zero a ha (p s))
      let m := smoothSpecialUnitaryProductIntegral n K
      Tendsto (fun t => m (e t * g t) - m (e 0) * Real.log (m (e 0))) atTop (𝓝 0)) :
    let e := smoothMatrixProductPositive a (p 0)
    let g := smoothMatrixProductLog e (smoothMatrixProductPositive_ne_zero a ha (p 0))
    let m := smoothSpecialUnitaryProductIntegral n K
    m (e*g) - m e * Real.log (m e) ≤
      m (e * derivationGamma (smoothSpecialUnitaryProductDerivative n K) g g) / n := by
  let e := fun s => smoothMatrixProductPositive a (p s)
  let g := fun s => smoothMatrixProductLog (e s) (smoothMatrixProductPositive_ne_zero a ha (p s))
  let D := smoothSpecialUnitaryProductDerivative n K
  let m := smoothSpecialUnitaryProductIntegral n K
  let ev := fun U : SpecialUnitaryProduct n K => smoothMatrixProductEvaluation (specialUnitaryProductVal U)
  have hn : (0:ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have he : ∀ s U, 0 < ev U (e s) := by
    intro s U
    exact ha.trans_le (smoothMatrixProductPositive_lower a ha (p s) (specialUnitaryProductVal U))
  have hexp : ∀ s i, D i (e s) = e s * D i (g s) := by
    intro s i
    exact smoothMatrixProductDerivative_log_chain (specialUnitaryProductFrame i) (e s) _
  have h := logSobolev_of_positive_heat (specialUnitaryProductHaar n K) ev m (fun _ => rfl) D
    (fun i => smoothRightMatrixProductDerivative_mul (specialUnitaryProductFrame i))
    (fun i f => smoothSpecialUnitaryProductIntegral_derivative_zero (specialUnitaryProductFrame i)
      (fun j => congrFun (specialUnitaryProductFrame_skew i) j) (specialUnitaryProductFrame_trace i) f)
    (fun f hf => smoothSpecialUnitaryProductIntegral_nonneg f hf)
    ((n:ℝ)/2) (by positivity)
    (fun f U => smoothSpecialUnitaryProduct_gamma_two_lower n K f (specialUnitaryProductVal U))
    e g he (fun _ _ => rfl) hexp
    hcont.1 hcont.2.1 hcont.2.2.1 hcont.2.2.2.1 hcont.2.2.2.2
    (clamped_product_heat_hasDerivAt p a ha hp htime)
    (clamped_product_heat_derivative_hasDerivAt p a ha hp hDtime) hlim
  have hden : 2 * ((n:ℝ)/2) = n := by ring
  simpa only [hden] using h

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ParametricSmooth -/
section
open scoped Matrix Matrix.Norms.L2Operator ContDiff

namespace BosonicLearn.Prop2
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Any linear family in a finite-dimensional space of smooth ambient functions
is jointly smooth in its coefficients and its ambient argument. -/
theorem contDiff_smoothMatrixProduct_linear_family [FiniteDimensional ℝ E]
    {n K : ℕ} (R : E →ₗ[ℝ] smoothMatrixProductFunctions n K) :
    ContDiff ℝ ∞ (fun p : E × MatrixProduct n K => R p.1 p.2) := by
  let b := Module.finBasis ℝ E
  have heq : (fun p : E × MatrixProduct n K => R p.1 p.2) =
      fun p => ∑ i, b.repr p.1 i * R (b i) p.2 := by
    funext p
    have h := congrArg (fun v : E => smoothMatrixProductEvaluation p.2 (R v)) (b.sum_repr p.1)
    simp only [map_sum, map_smul, smul_eq_mul] at h
    exact h.symm
  rw [heq]
  apply ContDiff.sum
  intro i hi
  have hc : ContDiff ℝ ∞ (fun v : E => b.repr v i) :=
    (b.coord i).toContinuousLinearMap.contDiff
  exact (hc.comp contDiff_fst).mul
    ((smoothMatrixProductFunctions_contDiff (R (b i))).comp contDiff_snd)

/-- Parameter-dependent invariant differentiation preserves joint smoothness. -/
theorem contDiff_smoothMatrixProduct_family_derivative
    {n K : ℕ} (f : E → smoothMatrixProductFunctions n K)
    (hf : ContDiff ℝ ∞ (fun p : E × MatrixProduct n K => f p.1 p.2))
    (B : MatrixProduct n K) :
    ContDiff ℝ ∞ (fun p : E × MatrixProduct n K =>
      smoothRightMatrixProductDerivative B (f p.1) p.2) := by
  have hf' : ContDiff ℝ ∞ (Function.uncurry
      (fun p : E × MatrixProduct n K => fun A : MatrixProduct n K => f p.1 A)) := by
    exact hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hf'.fderiv_apply contDiff_snd (contDiff_snd.mul contDiff_const) (by simp)

/-- Iterating a fixed finite sum-of-squares operator preserves joint smoothness. -/
theorem contDiff_smoothMatrixProduct_family_laplacian
    {n K : ℕ} {ι : Type*} [Fintype ι] (B : ι → MatrixProduct n K)
    (f : E → smoothMatrixProductFunctions n K)
    (hf : ContDiff ℝ ∞ (fun p : E × MatrixProduct n K => f p.1 p.2)) :
    ContDiff ℝ ∞ (fun p : E × MatrixProduct n K =>
      derivationLaplacian (fun i => smoothRightMatrixProductDerivative (B i)) (f p.1) p.2) := by
  have heq : (fun p : E × MatrixProduct n K =>
      derivationLaplacian (fun i => smoothRightMatrixProductDerivative (B i)) (f p.1) p.2) =
      fun p => ∑ i, smoothRightMatrixProductDerivative (B i)
        (smoothRightMatrixProductDerivative (B i) (f p.1)) p.2 := by
    funext p
    change smoothMatrixProductEvaluation p.2
      (derivationLaplacian (fun i => smoothRightMatrixProductDerivative (B i)) (f p.1)) = _
    rw [derivationLaplacian_apply, map_sum]
    rfl
  rw [heq]
  apply ContDiff.sum
  intro i hi
  exact contDiff_smoothMatrixProduct_family_derivative
    (fun v => smoothRightMatrixProductDerivative (B i) (f v))
    (contDiff_smoothMatrixProduct_family_derivative f hf (B i)) (B i)

/-- The carré du champ preserves joint smoothness of both arguments. -/
theorem contDiff_smoothMatrixProduct_family_gamma
    {n K : ℕ} {ι : Type*} [Fintype ι] (B : ι → MatrixProduct n K)
    (f g : E → smoothMatrixProductFunctions n K)
    (hf : ContDiff ℝ ∞ (fun p : E × MatrixProduct n K => f p.1 p.2))
    (hg : ContDiff ℝ ∞ (fun p : E × MatrixProduct n K => g p.1 p.2)) :
    ContDiff ℝ ∞ (fun p : E × MatrixProduct n K =>
      derivationGamma (fun i => smoothRightMatrixProductDerivative (B i)) (f p.1) (g p.1) p.2) := by
  have heq : (fun p : E × MatrixProduct n K =>
      derivationGamma (fun i => smoothRightMatrixProductDerivative (B i)) (f p.1) (g p.1) p.2) =
      fun p => ∑ i, smoothRightMatrixProductDerivative (B i) (f p.1) p.2 *
        smoothRightMatrixProductDerivative (B i) (g p.1) p.2 := by
    funext p
    change smoothMatrixProductEvaluation p.2
      (derivationGamma (fun i => smoothRightMatrixProductDerivative (B i)) (f p.1) (g p.1)) = _
    simp only [derivationGamma, map_sum, map_mul]
    rfl
  rw [heq]
  apply ContDiff.sum
  intro i hi
  exact (contDiff_smoothMatrixProduct_family_derivative f hf (B i)).mul
    (contDiff_smoothMatrixProduct_family_derivative g hg (B i))

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ClampedFamily -/
section
open scoped Matrix Matrix.Norms.L2Operator ContDiff

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

/-- All five joint continuity requirements in the entropy/Fisher heat-flow
argument follow from finite-dimensional smooth representatives. In particular,
none of the integration hypotheses needs to be postulated for polynomial heat. -/
theorem clamped_linear_family_joint_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n K : ℕ} {ι : Type*} [Fintype ι]
    (R : E →ₗ[ℝ] smoothMatrixProductFunctions n K)
    (B : ι → MatrixProduct n K) (a : ℝ) (ha : 0 < a) :
    let e := fun v : E => smoothMatrixProductPositive a (R v)
    let g := fun v : E => smoothMatrixProductLog (e v)
      (smoothMatrixProductPositive_ne_zero a ha (R v))
    let D := fun i => smoothRightMatrixProductDerivative (B i)
    ContDiff ℝ ∞ (fun p : E × MatrixProduct n K => e p.1 p.2) ∧
    ContDiff ℝ ∞ (fun p : E × MatrixProduct n K => g p.1 p.2) ∧
    ContDiff ℝ ∞ (fun p : E × MatrixProduct n K => derivationLaplacian D (e p.1) p.2) ∧
    ContDiff ℝ ∞ (fun p : E × MatrixProduct n K =>
      (e p.1 * derivationGamma D (g p.1) (g p.1)) p.2) ∧
    ContDiff ℝ ∞ (fun p : E × MatrixProduct n K =>
      (derivationLaplacian D (e p.1) * derivationGamma D (g p.1) (g p.1)) p.2 +
        2 * (e p.1 * derivationGamma D (g p.1)
          (derivationLaplacian D (g p.1) + derivationGamma D (g p.1) (g p.1))) p.2) := by
  dsimp only
  let e := fun v : E => smoothMatrixProductPositive a (R v)
  let g := fun v : E => smoothMatrixProductLog (e v)
    (smoothMatrixProductPositive_ne_zero a ha (R v))
  let D := fun i => smoothRightMatrixProductDerivative (B i)
  have he : ContDiff ℝ ∞ (fun p : E × MatrixProduct n K => e p.1 p.2) :=
    (smoothPositiveClamp_smooth a).comp (contDiff_smoothMatrixProduct_linear_family R)
  have hg : ContDiff ℝ ∞ (fun p : E × MatrixProduct n K => g p.1 p.2) :=
    he.log (fun p => smoothMatrixProductPositive_ne_zero a ha (R p.1) p.2)
  have hLe := contDiff_smoothMatrixProduct_family_laplacian B e he
  have hLg := contDiff_smoothMatrixProduct_family_laplacian B g hg
  have hG := contDiff_smoothMatrixProduct_family_gamma B g g hg hg
  have hH : ContDiff ℝ ∞ (fun p : E × MatrixProduct n K =>
      (derivationLaplacian D (g p.1) + derivationGamma D (g p.1) (g p.1)) p.2) := by
    exact hLg.add hG
  have hGH := contDiff_smoothMatrixProduct_family_gamma B g
    (fun v => derivationLaplacian D (g v) + derivationGamma D (g v) (g v)) hg hH
  exact ⟨he, hg, hLe, he.mul hG, (hLe.mul hG).add (contDiff_const.mul (he.mul hGH))⟩

/-- Restrict a jointly continuous ambient family along a continuous coefficient
curve and the product special-unitary inclusion. -/
theorem continuous_family_along_curve_on_specialUnitary
    {E : Type*} [TopologicalSpace E] {n K : ℕ}
    (f : E → MatrixProduct n K → ℝ)
    (hf : Continuous (fun p : E × MatrixProduct n K => f p.1 p.2))
    (q : ℝ → E) (hq : Continuous q) :
    Continuous (fun p : ℝ × SpecialUnitaryProduct n K =>
      f (q p.1) (specialUnitaryProductVal p.2)) := by
  exact hf.comp ((hq.comp continuous_fst).prodMk
    ((continuous_specialUnitaryProductVal n K).comp continuous_snd))

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2EntropyApproximation -/
section
open MeasureTheory Filter
open scoped Topology

namespace BosonicLearn.Prop2
noncomputable section

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
  [BorelSpace Ω] [CompactSpace Ω]
  (μ : Measure Ω) [IsFiniteMeasure μ]

/-- Integration is continuous for the uniform norm on continuous functions. -/
theorem continuous_continuousMap_integral :
    Continuous (fun f : C(Ω, ℝ) => ∫ x, f x ∂μ) := by
  have h := (MeasureTheory.continuous_integral (μ := μ) (G := ℝ)).comp
    (ContinuousMap.toLp 1 μ ℝ).continuous
  convert h using 1
  funext f
  exact (integral_congr_ae (ContinuousMap.coeFn_toLp (p := 1) (μ := μ) (𝕜 := ℝ) f)).symm

/-- The unnormalized entropy of a continuous density. Its formula extends
continuously even to functions that vanish. -/
def continuousDensityEntropy (f : C(Ω, ℝ)) : ℝ :=
  (∫ x, f x * Real.log (f x) ∂μ) -
    (∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ)

theorem continuous_continuousDensityEntropy :
    Continuous (continuousDensityEntropy μ) := by
  let q : C(ℝ, ℝ) := ⟨fun x => x * Real.log x, Real.continuous_mul_log⟩
  have hleft := (continuous_continuousMap_integral μ).comp q.continuous_postcomp
  have hright := Real.continuous_mul_log.comp (continuous_continuousMap_integral μ)
  exact hleft.sub hright

theorem continuousDensityEntropy_tendsto {ι : Type*} {l : Filter ι}
    {p : ι → C(Ω, ℝ)} {f : C(Ω, ℝ)} (hp : Tendsto p l (𝓝 f)) :
    Tendsto (fun i => continuousDensityEntropy μ (p i)) l
      (𝓝 (continuousDensityEntropy μ f)) :=
  (continuous_continuousDensityEntropy μ).continuousAt.tendsto.comp hp

/-- Uniform limits preserve entropy bounds with the same constant. -/
theorem continuousDensityEntropy_le_of_tendsto {ι : Type*} {l : Filter ι} [NeBot l]
    {p : ι → C(Ω, ℝ)} {f : C(Ω, ℝ)} (hp : Tendsto p l (𝓝 f)) (C : ℝ)
    (hbound : ∀ᶠ i in l, continuousDensityEntropy μ (p i) ≤ C * ∫ x, p i x ∂μ) :
    continuousDensityEntropy μ f ≤ C * ∫ x, f x ∂μ := by
  exact le_of_tendsto_of_tendsto (continuousDensityEntropy_tendsto μ hp)
    (((continuous_continuousMap_integral μ).continuousAt.tendsto.comp hp).const_mul C) hbound

theorem continuousDensityEntropy_const [IsProbabilityMeasure μ] (c : ℝ) :
    continuousDensityEntropy μ (ContinuousMap.const Ω c) = 0 := by
  simp [continuousDensityEntropy]

/-- Uniform equilibration to a constant forces entropy to vanish. -/
theorem continuousDensityEntropy_tendsto_zero {ι : Type*} {l : Filter ι}
    [IsProbabilityMeasure μ] {p : ι → C(Ω, ℝ)} {c : ℝ}
    (hp : Tendsto p l (𝓝 (ContinuousMap.const Ω c))) :
    Tendsto (fun i => continuousDensityEntropy μ (p i)) l (𝓝 0) := by
  simpa only [continuousDensityEntropy_const] using continuousDensityEntropy_tendsto μ hp

/-- This version uses the fixed equilibrium mass, as in the entropy-dissipation
identity for a mass-preserving heat trajectory. -/
theorem integral_mul_log_sub_const_tendsto_zero {ι : Type*} {l : Filter ι}
    [IsProbabilityMeasure μ] {p : ι → C(Ω, ℝ)} {c : ℝ}
    (hp : Tendsto p l (𝓝 (ContinuousMap.const Ω c))) :
    Tendsto (fun i => (∫ x, p i x * Real.log (p i x) ∂μ) - c * Real.log c)
      l (𝓝 0) := by
  let q : C(ℝ, ℝ) := ⟨fun x => x * Real.log x, Real.continuous_mul_log⟩
  have h := ((continuous_continuousMap_integral μ).comp q.continuous_postcomp).continuousAt.tendsto.comp hp
  simpa [q] using h.sub_const (c * Real.log c)

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ProductFisherBound -/
section
open MeasureTheory
open scoped Topology Matrix Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section

theorem smoothSpecialUnitaryProduct_gamma_le {n K : ℕ} (hn : 1 ≤ n)
    (f : smoothMatrixProductFunctions n K)
    (U : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ V W : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ,
      |f (fun i => (V i : Matrix (Fin n) (Fin n) ℂ)) -
        f (fun i => (W i : Matrix (Fin n) (Fin n) ℂ))| ≤
      L * Real.sqrt (∑ i, ∑ x, ∑ y,
        ‖(V i : Matrix (Fin n) (Fin n) ℂ) x y -
          (W i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2)) :
    smoothMatrixProductEvaluation (fun i => (U i : Matrix (Fin n) (Fin n) ℂ))
      (derivationGamma (smoothSpecialUnitaryProductDerivative n K) f f) ≤ L^2 := by
  rw [derivationGamma, map_sum]
  simp only [map_mul, smoothMatrixProductEvaluation_apply]
  simp only [← sq]
  rw [Fintype.sum_prod_type]
  exact smoothRightMatrixProductDerivative_energy_le hn f U L hL hLip

/-- An ambient smooth extension of log(p) has Fisher energy controlled by the
ambient Frobenius Lipschitz constant of log(p) on the group itself. -/
theorem specialUnitaryProduct_fisher_le {n K : ℕ} (hn : 1 ≤ n)
    (p : C(Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ, ℝ))
    (hp : ∀ U, 0 ≤ p U)
    (g : smoothMatrixProductFunctions n K)
    (hg : ∀ U : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ,
      g (fun i => (U i : Matrix (Fin n) (Fin n) ℂ)) = Real.log (p U))
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ U V : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ,
      |Real.log (p U) - Real.log (p V)| ≤ L * Real.sqrt
        (∑ i, ∑ x, ∑ y, ‖(U i : Matrix (Fin n) (Fin n) ℂ) x y -
          (V i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2)) :
    (∫ U, p U * smoothMatrixProductEvaluation (fun i => (U i : Matrix (Fin n) (Fin n) ℂ))
      (derivationGamma (smoothSpecialUnitaryProductDerivative n K) g g)
      ∂(Measure.pi (fun _ : Fin K => specialUnitaryHaar n))) ≤
    L^2 * ∫ U, p U ∂(Measure.pi (fun _ : Fin K => specialUnitaryHaar n)) := by
  letI : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin n) ℂ) := inferInstance
  let μ := Measure.pi (fun _ : Fin K => specialUnitaryHaar n)
  have hc : Continuous (fun U : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ =>
      smoothMatrixProductEvaluation (fun i => (U i : Matrix (Fin n) (Fin n) ℂ))
        (derivationGamma (smoothSpecialUnitaryProductDerivative n K) g g)) :=
    (smoothMatrixProductFunctions_contDiff _).continuous.comp
      (continuous_pi (fun i => continuous_subtype_val.comp (continuous_apply i)))
  have hleft := continuous_integrable_compact μ _ (p.continuous.mul hc)
  have hright := continuous_integrable_compact μ (fun U => L^2 * p U)
    (continuous_const.mul p.continuous)
  calc
    _ ≤ ∫ U, L^2 * p U ∂μ := by
      apply integral_mono hleft hright
      intro U
      change p U * smoothMatrixProductEvaluation (fun i => (U i : Matrix (Fin n) (Fin n) ℂ))
        (derivationGamma (smoothSpecialUnitaryProductDerivative n K) g g) ≤ L^2 * p U
      have h := smoothSpecialUnitaryProduct_gamma_le hn g U L hL (by simpa only [hg] using hLip)
      calc
        _ ≤ p U * L^2 := mul_le_mul_of_nonneg_left h (hp U)
        _ = _ := mul_comm _ _
    _ = _ := integral_const_mul _ _

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ProductPolynomialLogSobolev -/
section
open MeasureTheory Filter Set
open scoped Topology Matrix Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 1800000

/-- The actual polynomial heat, after a harmless positive extension off the
group, proves the logarithmic Sobolev inequality with constant 1/n. -/
theorem specialUnitaryProductPolynomialHeat_logSobolev {n K d : ℕ} [NeZero n]
    (f : specialUnitaryProductPolynomialHilbert n K d) (a : ℝ) (ha : 0 < a)
    (hf : ∀ U : SpecialUnitaryProduct n K, 2*a ≤
      continuousL2Representative (specialUnitaryProductHaar n K)
        (specialUnitaryProductPolynomialSpace n K d) f U) :
    let p := specialUnitaryProductSmoothHeat n K d f
    let e := smoothMatrixProductPositive a (p 0)
    let g := smoothMatrixProductLog e (smoothMatrixProductPositive_ne_zero a ha (p 0))
    let m := smoothSpecialUnitaryProductIntegral n K
    m (e*g) - m e * Real.log (m e) ≤
      m (e * derivationGamma (smoothSpecialUnitaryProductDerivative n K) g g) / n := by
  let p := specialUnitaryProductSmoothHeat n K d f
  let e := fun t => smoothMatrixProductPositive a (p t)
  let g := fun t => smoothMatrixProductLog (e t) (smoothMatrixProductPositive_ne_zero a ha (p t))
  let m := smoothSpecialUnitaryProductIntegral n K
  let μ := specialUnitaryProductHaar n K
  let c := ∫ U, continuousL2Representative μ (specialUnitaryProductPolynomialSpace n K d) f U ∂μ
  have hp : ∀ t : ℝ, 0 ≤ t → ∀ U : SpecialUnitaryProduct n K,
      2*a ≤ p t (specialUnitaryProductVal U) :=
    fun t ht => specialUnitaryProductSmoothHeat_preserves_lower f (2*a) hf t ht
  have hq : Continuous (fun t => specialUnitaryProductPolynomialHeat n K d t f) :=
    continuous_iff_continuousAt.mpr (fun t => (specialUnitaryProductPolynomialHeat_hasDerivAt n K d f t).continuousAt)
  obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ := clamped_linear_family_joint_smooth
    (specialUnitaryProductPolynomialSmoothLift n K d) (@specialUnitaryProductFrame n K) a ha
  have hmap : Continuous (fun z : ℝ × SpecialUnitaryProduct n K =>
      (specialUnitaryProductPolynomialHeat n K d z.1 f, specialUnitaryProductVal z.2)) :=
    (hq.comp continuous_fst).prodMk ((continuous_specialUnitaryProductVal n K).comp continuous_snd)
  have hc := And.intro (hc1.continuous.comp hmap) (And.intro (hc2.continuous.comp hmap)
    (And.intro (hc3.continuous.comp hmap) (And.intro (hc4.continuous.comp hmap)
      (hc5.continuous.comp hmap))))
  have hmean : Tendsto (fun t => smoothSpecialUnitaryProductRestriction n K (p t)) atTop
      (𝓝 (ContinuousMap.const (SpecialUnitaryProduct n K) c)) := by
    convert specialUnitaryProductSmoothHeat_tendsto_mean f using 1
    congr 1
    ext U
    simp [c, μ]
  have hm0 : m (e 0) = c := by
    change (∫ U, e 0 (specialUnitaryProductVal U) ∂μ) = c
    calc
      _ = ∫ U, p 0 (specialUnitaryProductVal U) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun U =>
          smoothMatrixProductPositive_eq_on_group a ha (p 0) (hp 0 le_rfl) U)
      _ = c := specialUnitaryProductSmoothHeat_integral f 0
  have hlim : Tendsto (fun t => m (e t * g t) - m (e 0) * Real.log (m (e 0))) atTop (𝓝 0) := by
    have hraw := integral_mul_log_sub_const_tendsto_zero μ hmean
    apply hraw.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    rw [hm0]
    congr 1
    change (∫ U, p t (specialUnitaryProductVal U) * Real.log (p t (specialUnitaryProductVal U)) ∂μ) =
      ∫ U, e t (specialUnitaryProductVal U) * g t (specialUnitaryProductVal U) ∂μ
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun U => by
      dsimp only [g]
      rw [smoothMatrixProductLog_apply, smoothMatrixProductPositive_eq_on_group a ha (p t) (hp t ht) U])
  exact product_logSobolev_of_clamped_heat p a ha hp
    (fun t ht U => specialUnitaryProductSmoothHeat_hasDerivAt f t U)
    (fun t ht b U => specialUnitaryProductSmoothHeat_derivative_hasDerivAt f
      (specialUnitaryProductFrame b) (fun i => congrFun (specialUnitaryProductFrame_skew b) i)
      (specialUnitaryProductFrame_trace b) t U) hc hlim

/-- Every strictly positive polynomial density on the product group satisfies
the exact log-Lipschitz entropy bound needed for the final Haar concentration. -/
theorem specialUnitaryProduct_polynomial_logSobolev (n K : ℕ) (hn : 1 ≤ n)
    (d : ℕ) (p : C(SpecialUnitaryProduct n K, ℝ))
    (hp : p ∈ specialUnitaryProductPolynomialSpace n K d) (hpos : ∀ U, 0 < p U)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ U V : SpecialUnitaryProduct n K,
      |Real.log (p U) - Real.log (p V)| ≤ L * Real.sqrt
        (∑ i, ∑ x, ∑ y, ‖(U i : Matrix (Fin n) (Fin n) ℂ) x y -
          (V i : Matrix (Fin n) (Fin n) ℂ) x y‖^2)) :
    continuousDensityEntropy (Measure.pi (fun _ : Fin K => specialUnitaryHaar n)) p ≤
      L^2 / n * ∫ U, p U ∂(Measure.pi (fun _ : Fin K => specialUnitaryHaar n)) := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨q, hq⟩ := hp
  let f := matrixProductPolynomialHilbertImage n K d q
  have hrep : continuousL2Representative (specialUnitaryProductHaar n K)
      (specialUnitaryProductPolynomialSpace n K d) f = p :=
    (matrixProductPolynomialHilbertImage_representative q).trans hq
  obtain ⟨U₀, hU₀, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty p.continuous.continuousOn
  let a : ℝ := p U₀ / 4
  have ha : 0 < a := div_pos (hpos U₀) (by norm_num)
  have hpa (U : SpecialUnitaryProduct n K) : 2*a ≤ p U := by
    have h : p U₀ ≤ p U := hmin (Set.mem_univ U)
    dsimp only [a]
    linarith [hpos U₀]
  let pheat := specialUnitaryProductSmoothHeat n K d f
  let e := smoothMatrixProductPositive a (pheat 0)
  let g := smoothMatrixProductLog e (smoothMatrixProductPositive_ne_zero a ha (pheat 0))
  let m := smoothSpecialUnitaryProductIntegral n K
  have hstart (U : SpecialUnitaryProduct n K) : pheat 0 (specialUnitaryProductVal U) = p U :=
    congrArg (fun q : C(SpecialUnitaryProduct n K, ℝ) => q U)
      ((specialUnitaryProductSmoothHeat_zero f).trans hrep)
  have he (U : SpecialUnitaryProduct n K) : e (specialUnitaryProductVal U) = p U := by
    exact (smoothMatrixProductPositive_eq_on_group a ha (pheat 0)
      (fun V => by rw [hstart]; exact hpa V) U).trans (hstart U)
  have hg (U : SpecialUnitaryProduct n K) : g (specialUnitaryProductVal U) = Real.log (p U) := by
    change Real.log (e (specialUnitaryProductVal U)) = _
    rw [he]
  have hs := specialUnitaryProductPolynomialHeat_logSobolev f a ha
    (fun U => by rw [hrep]; exact hpa U)
  have hleft : m (e*g) - m e * Real.log (m e) =
      continuousDensityEntropy (specialUnitaryProductHaar n K) p := by
    change (∫ U, e (specialUnitaryProductVal U) * g (specialUnitaryProductVal U) ∂specialUnitaryProductHaar n K) -
      (∫ U, e (specialUnitaryProductVal U) ∂specialUnitaryProductHaar n K) *
        Real.log (∫ U, e (specialUnitaryProductVal U) ∂specialUnitaryProductHaar n K) = _
    simp_rw [he, hg]
    rfl
  change m (e*g) - m e * Real.log (m e) ≤
    m (e * derivationGamma (smoothSpecialUnitaryProductDerivative n K) g g) / n at hs
  rw [hleft] at hs
  have hfish := specialUnitaryProduct_fisher_le hn p (fun U => (hpos U).le) g hg L hL hLip
  have hright : m (e * derivationGamma (smoothSpecialUnitaryProductDerivative n K) g g) ≤
      L^2 * ∫ U, p U ∂specialUnitaryProductHaar n K := by
    change (∫ U, e (specialUnitaryProductVal U) *
      derivationGamma (smoothSpecialUnitaryProductDerivative n K) g g (specialUnitaryProductVal U)
      ∂specialUnitaryProductHaar n K) ≤ _
    simp_rw [he]
    exact hfish
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  calc
    _ ≤ m (e * derivationGamma (smoothSpecialUnitaryProductDerivative n K) g g) / n := hs
    _ ≤ (L^2 * ∫ U, p U ∂specialUnitaryProductHaar n K) / n := div_le_div_of_nonneg_right hright hn0
    _ = _ := by dsimp only [specialUnitaryProductHaar]; ring

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2LogPeakApproximation -/
section
open MeasureTheory MeasureTheory.Measure Filter Set TopologicalSpace
open scoped Topology Matrix Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 900000

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MetrizableSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsFiniteMeasure μ] [IsOpenPosMeasure μ]

def continuousExp (F : C(G, ℝ)) : C(G, ℝ) := ⟨fun U => Real.exp (F U), F.continuous.rexp⟩

theorem peakConvolution_le_mul (c : C(G, ℝ)) (hc : ∀ V, 0 ≤ c V)
    (hc1 : 0 < c 1) (m : ℕ) (F : C(G, ℝ)) (U V : G) (a : ℝ)
    (hF : ∀ W, F (U * W) ≤ a * F (V * W)) :
    peakConvolution μ c m F U ≤ a * peakConvolution μ c m F V := by
  have hi (U : G) : Integrable (fun W => c W ^ m * F (U * W)) μ :=
    continuous_integrable_compact μ _
      ((c.continuous.pow m).mul (F.continuous.comp (continuous_const.mul continuous_id)))
  rw [peakConvolution_apply, peakConvolution_apply]
  calc
    _ ≤ (∫ W, c W ^ m ∂μ)⁻¹ * ∫ W, a * (c W ^ m * F (V * W)) ∂μ := by
      apply mul_le_mul_of_nonneg_left _
        (inv_nonneg.mpr (peak_power_integral_pos μ c hc hc1 m).le)
      apply integral_mono (hi U) ((hi V).const_mul a)
      intro W
      nlinarith [mul_le_mul_of_nonneg_left (hF W) (pow_nonneg (hc W) m)]
    _ = _ := by rw [integral_const_mul]; ring

theorem peakConvolution_exp_pos (c : C(G, ℝ)) (hc : ∀ V, 0 ≤ c V)
    (hc1 : 0 < c 1) (m : ℕ) (F : C(G, ℝ)) (U : G) :
    0 < peakConvolution μ c m (continuousExp F) U := by
  rw [peakConvolution_apply]
  apply mul_pos (inv_pos.mpr (peak_power_integral_pos μ c hc hc1 m))
  have hcont : Continuous (fun W => c W ^ m * Real.exp (F (U * W))) :=
    (c.continuous.pow m).mul (F.continuous.comp (continuous_const.mul continuous_id)).rexp
  apply integral_pos_of_integrable_nonneg_nonzero hcont
    (continuous_integrable_compact μ _ hcont)
    (fun W => mul_nonneg (pow_nonneg (hc W) m) (Real.exp_pos _).le)
  exact (mul_pos (pow_pos hc1 m) (Real.exp_pos (F (U * 1)))).ne'

/-- Positive averaging preserves log-Lipschitz bounds. This is the key to
approximating exponential densities without needing convergence of derivatives. -/
theorem log_peakConvolution_exp_abs_sub_le (c : C(G, ℝ)) (hc : ∀ V, 0 ≤ c V)
    (hc1 : 0 < c 1) (m : ℕ) (F : C(G, ℝ)) (U V : G) (B : ℝ)
    (hF : ∀ W, |F (U * W) - F (V * W)| ≤ B) :
    |Real.log (peakConvolution μ c m (continuousExp F) U) -
      Real.log (peakConvolution μ c m (continuousExp F) V)| ≤ B := by
  have hpos (W : G) := peakConvolution_exp_pos μ c hc hc1 m F W
  have hcompare (U V : G) (hUV : ∀ W, F (U * W) - F (V * W) ≤ B) :
      Real.log (peakConvolution μ c m (continuousExp F) U) -
        Real.log (peakConvolution μ c m (continuousExp F) V) ≤ B := by
    have hm := peakConvolution_le_mul μ c hc hc1 m (continuousExp F) U V (Real.exp B) (by
      intro W
      change Real.exp (F (U * W)) ≤ Real.exp B * Real.exp (F (V * W))
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [hUV W]))
    have hl := Real.log_le_log (hpos U) hm
    rw [Real.log_mul (Real.exp_pos B).ne' (hpos V).ne', Real.log_exp] at hl
    linarith
  apply abs_sub_le_iff.mpr
  exact ⟨hcompare U V (fun W => (abs_sub_le_iff.mp (hF W)).1),
    hcompare V U (fun W => (abs_sub_le_iff.mp (hF W)).2)⟩

theorem specialUnitary_log_peakConvolution_exp_lipschitz (n K : ℕ) (hn : 1 ≤ n)
    (F : C(Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ, ℝ)) (L : ℝ)
    (hLip : ∀ U V : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ,
      |F U - F V| ≤ L * Real.sqrt (∑ i, ∑ x, ∑ y,
        ‖(U i : Matrix (Fin n) (Fin n) ℂ) x y -
          (V i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2))
    (m : ℕ) (U V : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ) :
    |Real.log (peakConvolution (Measure.pi (fun _ : Fin K => specialUnitaryHaar n))
        (specialUnitaryProductPeak n K) m (continuousExp F) U) -
      Real.log (peakConvolution (Measure.pi (fun _ : Fin K => specialUnitaryHaar n))
        (specialUnitaryProductPeak n K) m (continuousExp F) V)| ≤
      L * Real.sqrt (∑ i, ∑ x, ∑ y,
        ‖(U i : Matrix (Fin n) (Fin n) ℂ) x y -
          (V i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2) := by
  letI : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin n) ℂ) := inferInstance
  apply log_peakConvolution_exp_abs_sub_le _ _ (specialUnitaryProductPeak_nonneg n K hn)
    (by rw [specialUnitaryProductPeak_one n K hn]; norm_num)
  intro W
  simpa only [specialUnitaryProductFrobenius_right_mul] using hLip (U * W) (V * W)

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ProductPolynomialApproximation -/
section
open MeasureTheory Filter
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 1200000

/-- Any real-linear matrix functional as an element of the ambient smooth algebra. -/
def smoothMatrixProductLinearForm {n K : ℕ} (ℓ : MatrixProduct n K →ₗ[ℝ] ℝ) :
    smoothMatrixProductFunctions n K :=
  ⟨ℓ, by
    change ContDiff ℝ ∞ (ℓ : MatrixProduct n K → ℝ)
    exact ℓ.toContinuousLinearMap.contDiff⟩

theorem smoothMatrixProductLinearForm_expansion {n K : ℕ}
    (ℓ : MatrixProduct n K →ₗ[ℝ] ℝ) :
    smoothMatrixProductLinearForm ℓ = ∑ j, ℓ (matrixProductPolynomialBasis n K j) • smoothMatrixProductCoordinate n K j := by
  apply Subtype.ext
  funext A
  have h := congrArg ℓ ((matrixProductPolynomialBasis n K).sum_repr A)
  rw [map_sum] at h
  simp only [map_smul, smul_eq_mul] at h
  change ℓ A = smoothMatrixProductEvaluation A (∑ j, ℓ (matrixProductPolynomialBasis n K j) • smoothMatrixProductCoordinate n K j)
  rw [map_sum]
  calc
    _ = ∑ j, (matrixProductPolynomialBasis n K).repr A j * ℓ (matrixProductPolynomialBasis n K j) := h.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul]
      change _ = ℓ (matrixProductPolynomialBasis n K j) * (matrixProductPolynomialBasis n K).coord j A
      simp only [Module.Basis.coord_apply]
      ring

theorem smoothMatrixProductLinearForm_mem_generatorSpan {n K : ℕ}
    (ℓ : MatrixProduct n K →ₗ[ℝ] ℝ) :
    smoothMatrixProductLinearForm ℓ ∈ Submodule.span ℝ (Set.range (matrixProductPolynomialGenerator n K)) := by
  rw [smoothMatrixProductLinearForm_expansion]
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact Submodule.subset_span (Set.mem_range_self (some j))

def realTraceAdjointMulAt {n K : ℕ} (i : Fin K) (W : Matrix (Fin n) (Fin n) ℂ) :
    MatrixProduct n K →ₗ[ℝ] ℝ :=
  (realTraceAdjointMul W).comp (LinearMap.proj i)

def affineProductPeakPolynomial {n K : ℕ} (i : Fin K)
    (W : Matrix (Fin n) (Fin n) ℂ) : smoothMatrixProductFunctions n K :=
  (1 / 2 : ℝ) • (1 : smoothMatrixProductFunctions n K) +
    (1 / (2 * (n : ℝ)) : ℝ) • smoothMatrixProductLinearForm (realTraceAdjointMulAt i W)

theorem affineProductPeakPolynomial_mem_generatorSpan {n K : ℕ}
    (i : Fin K) (W : Matrix (Fin n) (Fin n) ℂ) :
    affineProductPeakPolynomial i W ∈
      Submodule.span ℝ (Set.range (matrixProductPolynomialGenerator n K)) := by
  apply Submodule.add_mem
  · apply Submodule.smul_mem
    exact Submodule.subset_span (Set.mem_range_self none)
  · exact Submodule.smul_mem _ _ (smoothMatrixProductLinearForm_mem_generatorSpan _)

theorem affineProductPeakPolynomial_restrict {n K : ℕ} (i : Fin K)
    (W U : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ) :
    affineProductPeakPolynomial i (W i : Matrix (Fin n) (Fin n) ℂ)
      (fun j => (U j : Matrix (Fin n) (Fin n) ℂ)) = specialUnitaryPeak n ((U⁻¹ * W) i) := by
  change (1 / 2 : ℝ) * 1 + (1 / (2 * (n : ℝ))) *
      ((U i : Matrix (Fin n) (Fin n) ℂ)ᴴ * W i).trace.re =
    (1 + ((U i : Matrix (Fin n) (Fin n) ℂ)ᴴ * W i).trace.re / n) / 2
  ring

theorem productPeakKernel_has_matrixPolynomial (n K m : ℕ)
    (W : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ) :
    ∃ f : smoothMatrixProductFunctions n K, f ∈ matrixProductPolynomialSpace n K (K * m) ∧
      ∀ U : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ,
        f (fun i => (U i : Matrix (Fin n) (Fin n) ℂ)) =
          peakKernelFamily (specialUnitaryProductPeak n K) m W U := by
  let f : smoothMatrixProductFunctions n K :=
    (∏ i, affineProductPeakPolynomial i (W i : Matrix (Fin n) (Fin n) ℂ)) ^ m
  have hf : f ∈ matrixProductPolynomialSpace n K (K * m) :=
    finitePolynomialSpace_pow_mem (matrixProductPolynomialGenerator n K) K
      (generatorSpan_finprod_mem _ K _ (fun i => affineProductPeakPolynomial_mem_generatorSpan i _)) m
  refine ⟨f, hf, ?_⟩
  intro U
  change smoothMatrixProductEvaluation (fun i => (U i : Matrix (Fin n) (Fin n) ℂ))
    ((∏ i, affineProductPeakPolynomial i (W i : Matrix (Fin n) (Fin n) ℂ)) ^ m) = _
  rw [map_pow, map_prod]
  change (∏ i, affineProductPeakPolynomial i (W i : Matrix (Fin n) (Fin n) ℂ)
    (fun j => (U j : Matrix (Fin n) (Fin n) ℂ))) ^ m = _
  simp_rw [affineProductPeakPolynomial_restrict]
  rfl

theorem productPeakKernel_mem_polynomialSpace (n K m : ℕ)
    (W : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ) :
    peakKernelFamily (specialUnitaryProductPeak n K) m W ∈
      specialUnitaryProductPolynomialSpace n K (K * m) := by
  obtain ⟨f, hf, heq⟩ := productPeakKernel_has_matrixPolynomial n K m W
  refine ⟨⟨f, hf⟩, ?_⟩
  ext U
  exact heq U

theorem productPeakConvolution_mem_polynomialSpace (n K m : ℕ)
    (F : C(Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ, ℝ)) :
    peakConvolution (Measure.pi (fun _ : Fin K => specialUnitaryHaar n))
      (specialUnitaryProductPeak n K) m F ∈
      specialUnitaryProductPolynomialSpace n K (K * m) := by
  letI : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin n) ℂ) := inferInstance
  exact peakConvolution_mem_of_kernels_mem (Measure.pi (fun _ : Fin K => specialUnitaryHaar n))
    (specialUnitaryProductPolynomialSpace n K (K * m)) (specialUnitaryProductPeak n K) m F
    (productPeakKernel_mem_polynomialSpace n K m)

/-- Positive polynomial densities approximate exp(F) uniformly and retain the
same log-Lipschitz constant. This is sufficient to pass polynomial density LSI to
the exponential moments required by Herbst, without C1 approximation. -/
theorem specialUnitary_positive_polynomial_approximation (n K : ℕ) (hn : 1 ≤ n)
    (F : C(Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ, ℝ)) (L : ℝ)
    (hLip : ∀ U V : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ,
      |F U - F V| ≤ L * Real.sqrt (∑ i, ∑ x, ∑ y,
        ‖(U i : Matrix (Fin n) (Fin n) ℂ) x y -
          (V i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2)) :
    ∃ p : ℕ → C(Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ, ℝ),
      Tendsto p atTop (𝓝 (continuousExp F)) ∧
      (∀ m, p m ∈ specialUnitaryProductPolynomialSpace n K (K * m)) ∧
      (∀ m U, 0 < p m U) ∧
      ∀ m U V, |Real.log (p m U) - Real.log (p m V)| ≤
        L * Real.sqrt (∑ i, ∑ x, ∑ y,
          ‖(U i : Matrix (Fin n) (Fin n) ℂ) x y -
            (V i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2) := by
  letI : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin n) ℂ) := inferInstance
  refine ⟨fun m => peakConvolution (Measure.pi (fun _ : Fin K => specialUnitaryHaar n))
    (specialUnitaryProductPeak n K) m (continuousExp F),
    specialUnitary_peakConvolution_tendsto n K hn (continuousExp F),
    fun m => productPeakConvolution_mem_polynomialSpace n K m (continuousExp F), ?_,
    specialUnitary_log_peakConvolution_exp_lipschitz n K hn F L hLip⟩
  intro m U
  exact peakConvolution_exp_pos _ _ (specialUnitaryProductPeak_nonneg n K hn)
    (by rw [specialUnitaryProductPeak_one n K hn]; norm_num) m F U



end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2PolynomialLogSobolevClosure -/
section
open MeasureTheory Filter
open scoped Topology Matrix Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section

/-- Polynomial-density logarithmic Sobolev with logarithmic Lipschitz control
already implies the full Lipschitz exponential-mean bound. Positive polynomial
approximation and entropy continuity discharge all approximation steps. -/
theorem specialUnitary_logmean_of_polynomial_logSobolev
    (n K : ℕ) (hn : 1 ≤ n)
    (hpoly : ∀ (d : ℕ)
      (p : C(Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ, ℝ)),
      p ∈ specialUnitaryProductPolynomialSpace n K d →
      (∀ U, 0 < p U) → ∀ (L : ℝ), 0 ≤ L →
      (∀ U V : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ,
        |Real.log (p U) - Real.log (p V)| ≤ L * Real.sqrt
          (∑ i, ∑ x, ∑ y, ‖(U i : Matrix (Fin n) (Fin n) ℂ) x y -
            (V i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2)) →
      continuousDensityEntropy (Measure.pi (fun _ : Fin K => specialUnitaryHaar n)) p ≤
        L^2 / n * ∫ U, p U ∂(Measure.pi (fun _ : Fin K => specialUnitaryHaar n)))
    (F : C(Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ, ℝ)) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ U V : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ,
      |F U - F V| ≤ L * Real.sqrt
        (∑ i, ∑ x, ∑ y, ‖(U i : Matrix (Fin n) (Fin n) ℂ) x y -
          (V i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2)) :
    Real.log (∫ U, Real.exp (F U) ∂(Measure.pi (fun _ : Fin K => specialUnitaryHaar n))) -
      L^2 / n ≤ ∫ U, F U ∂(Measure.pi (fun _ : Fin K => specialUnitaryHaar n)) := by
  letI : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin n) ℂ) := inferInstance
  let μ := Measure.pi (fun _ : Fin K => specialUnitaryHaar n)
  have hint (s : ℝ) : Integrable (fun U => Real.exp (s * F U)) μ :=
    continuous_integrable_compact μ _ ((continuous_const.mul F.continuous).rexp)
  have hent (s : ℝ) (hs : 0 < s) :
      (∫ U, s * F U * Real.exp (s * F U) ∂μ) -
        (∫ U, Real.exp (s * F U) ∂μ) * Real.log (∫ U, Real.exp (s * F U) ∂μ) ≤
      (L^2 / n) * s^2 * ∫ U, Real.exp (s * F U) ∂μ := by
    have hsLip : ∀ U V : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ,
        |(s • F) U - (s • F) V| ≤ (s * L) * Real.sqrt
          (∑ i, ∑ x, ∑ y, ‖(U i : Matrix (Fin n) (Fin n) ℂ) x y -
            (V i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2) := by
      intro U V
      simp only [ContinuousMap.smul_apply, smul_eq_mul, ← mul_sub, abs_mul, abs_of_pos hs]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hLip U V) hs.le
    obtain ⟨p, hp, hmem, hpos, hlog⟩ :=
      specialUnitary_positive_polynomial_approximation n K hn (s • F) (s * L) hsLip
    have hbound := continuousDensityEntropy_le_of_tendsto μ hp ((s * L)^2 / n)
      (Filter.Eventually.of_forall (fun m => hpoly (K*m) (p m) (hmem m) (hpos m)
        (s*L) (mul_nonneg hs.le hL) (hlog m)))
    simp only [continuousDensityEntropy, continuousExp, ContinuousMap.coe_mk,
      ContinuousMap.smul_apply, smul_eq_mul, Real.log_exp] at hbound
    convert hbound using 1
    · congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun U => mul_comm _ _)
    · ring
  have h := Prop5.logmean_le_mean_add_of_entropy μ F (L^2 / n) hint hent
  linarith

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2LogMeanProductCore -/
section
open MeasureTheory ProbabilityTheory

namespace BosonicLearn.Prop2
noncomputable section

/-- Conditional log-mean estimates add under a product measure. This is the
exponential-moment form of the tensorization step used in concentration. -/
theorem logmean_prod_le_of_logmean_sections {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : A × B → ℝ) (hF : Integrable F (μ.prod ν))
    (hExp : Integrable (fun p => Real.exp (F p)) (μ.prod ν))
    (hExpMean : Integrable (fun a => Real.exp (∫ b, F (a, b) ∂ν)) μ)
    (c d : ℝ)
    (hsection : ∀ᵐ a ∂μ, Real.log (∫ b, Real.exp (F (a, b)) ∂ν) ≤
      (∫ b, F (a, b) ∂ν) + c)
    (hmean : Real.log (∫ a, Real.exp (∫ b, F (a, b) ∂ν) ∂μ) ≤
      (∫ a, ∫ b, F (a, b) ∂ν ∂μ) + d) :
    Real.log (∫ p, Real.exp (F p) ∂μ.prod ν) ≤ (∫ p, F p ∂μ.prod ν) + c + d := by
  have hpoint : ∀ᵐ a ∂μ, (∫ b, Real.exp (F (a, b)) ∂ν) ≤
      Real.exp c * Real.exp (∫ b, F (a, b) ∂ν) := by
    filter_upwards [hsection, hExp.prod_right_ae] with a ha hi
    have hp := integral_exp_pos hi
    have h := Real.exp_le_exp.mpr ha
    rw [Real.exp_log hp, Real.exp_add] at h
    simpa only [mul_comm] using h
  have hbound := integral_mono_ae hExp.integral_prod_left (hExpMean.const_mul (Real.exp c)) hpoint
  rw [integral_const_mul, ← integral_prod _ hExp] at hbound
  have hpos := integral_exp_pos hExp
  have hpmean := integral_exp_pos hExpMean
  have hlog := Real.log_le_log hpos hbound
  rw [Real.log_mul (Real.exp_pos c).ne' hpmean.ne', Real.log_exp] at hlog
  rw [← integral_prod F hF] at hmean
  linarith

/-- Integration preserves a pointwise Lipschitz bound, when both sections are integrable. -/
theorem abs_integral_sections_sub_le {A B : Type*} [MeasurableSpace B]
    (ν : Measure B) [IsProbabilityMeasure ν] (F : A → B → ℝ)
    (x y : A) (hx : Integrable (F x) ν) (hy : Integrable (F y) ν)
    (D : ℝ) (hD : ∀ᵐ b ∂ν, |F x b - F y b| ≤ D) :
    |(∫ b, F x b ∂ν) - ∫ b, F y b ∂ν| ≤ D := by
  rw [← integral_sub hx hy]
  calc
    _ ≤ ∫ b, |F x b - F y b| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ _b, D ∂ν := integral_mono_ae (hx.sub hy).abs (integrable_const D) hD
    _ = D := by simp

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2PhaseProductConcentration -/
section
open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 800000

def UnitaryProductLogMeanBound (n K : ℕ)
    (ν : Measure (Fin K → Matrix.unitaryGroup (Fin n) ℂ)) (c : ℝ) : Prop :=
  ∀ (F : (Fin K → Matrix.unitaryGroup (Fin n) ℂ) → ℝ), Continuous F →
    ∀ L : ℝ, 0 ≤ L →
    (∀ U V, |F U - F V| ≤ L * unitaryProductFrobeniusDist U V) →
    Real.log (∫ U, Real.exp (F U) ∂ν) ≤ (∫ U, F U ∂ν) + c * L ^ 2 / n

def EuclideanLogMeanBound (K : ℕ) (μ : Measure (Fin K → ℝ)) (c : ℝ) : Prop :=
  ∀ (F : (Fin K → ℝ) → ℝ), Continuous F →
    ∀ L : ℝ, 0 ≤ L →
    (∀ θ φ, |F θ - F φ| ≤ L * Real.sqrt (∑ i, (θ i - φ i) ^ 2)) →
    Real.log (∫ θ, Real.exp (F θ) ∂μ) ≤ (∫ θ, F θ ∂μ) + c * L ^ 2

/-- The product metric agrees exactly with the entrywise Hilbert--Schmidt metric
appearing in the original concentration theorem. -/
theorem unitaryProductFrobeniusDist_eq_entry {n K : ℕ}
    (U V : Fin K → Matrix.unitaryGroup (Fin n) ℂ) :
    unitaryProductFrobeniusDist U V = Real.sqrt (∑ i, ∑ x, ∑ y,
      ‖(U i : Matrix (Fin n) (Fin n) ℂ) x y -
        (V i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2) := by
  unfold unitaryProductFrobeniusDist
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Prop5.schatten_two_eq_sqrt, Real.sq_sqrt (by positivity)]
  exact Finset.sum_comm

theorem integrable_continuous_comp_compact {Ω T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace T] [TopologicalSpace T]
    [BorelSpace T] [CompactSpace T]
    (μ : Measure Ω) [IsFiniteMeasure μ] (g : Ω → T) (hg : Measurable g)
    (F : T → ℝ) (hF : Continuous F) : Integrable (fun x => F (g x)) μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  exact Integrable.of_bound (hF.measurable.comp hg).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => hC (g x) (Set.mem_univ _))

/-- The short-phase cube and special-unitary product bounds combine without a
factor depending on the number `K` of independent unitary matrices. -/
theorem unitary_product_logmean_of_phase_factorization (n K : ℕ) (hn : 1 ≤ n)
    (μ : Measure (Fin K → ℝ)) (ν : Measure (Fin K → Matrix.unitaryGroup (Fin n) ℂ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hmap : (μ.prod ν).map (fun p => phaseCubeMultiply p.1 p.2) =
      Measure.pi (fun _ : Fin K => unitaryHaar n))
    (cSU cPhase : ℝ)
    (hSU : UnitaryProductLogMeanBound n K ν cSU)
    (hPhase : EuclideanLogMeanBound K μ (cPhase / (n : ℝ) ^ 2)) :
    UnitaryProductLogMeanBound n K (Measure.pi (fun _ : Fin K => unitaryHaar n))
      (cSU + cPhase) := by
  letI : SecondCountableTopology (Matrix.unitaryGroup (Fin n) ℂ) := inferInstance
  intro F hF L hL hLip
  let f : (Fin K → ℝ) × (Fin K → Matrix.unitaryGroup (Fin n) ℂ) → ℝ :=
    fun p => F (phaseCubeMultiply p.1 p.2)
  let g : (Fin K → ℝ) → ℝ := fun θ => ∫ U, f (θ, U) ∂ν
  have hp := (continuous_phaseCubeMultiply n K).measurable
  have hi := integrable_continuous_comp_compact (μ.prod ν) _ hp F hF
  have hei := integrable_continuous_comp_compact (μ.prod ν) _ hp
    (fun U => Real.exp (F U)) (Real.continuous_exp.comp hF)
  have hc : Continuous (fun p : (Fin K → ℝ) × (Fin K → Matrix.unitaryGroup (Fin n) ℂ) =>
      F (phaseCubeMultiply p.1 p.2)) := hF.comp (continuous_phaseCubeMultiply n K)
  have hg : Continuous g := by
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous (μ := ν) (f := fun θ U => f (θ, U)) hc isCompact_univ)
  have hθ (θ : Fin K → ℝ) :
      Continuous (fun U : Fin K → Matrix.unitaryGroup (Fin n) ℂ => phaseCubeMultiply θ U) := by
    have hpair : Continuous (fun U : Fin K → Matrix.unitaryGroup (Fin n) ℂ => (θ, U)) :=
      continuous_const.prodMk continuous_id
    exact (continuous_phaseCubeMultiply n K).comp hpair
  have hfi (θ : Fin K → ℝ) : Integrable (fun U => f (θ, U)) ν :=
    integrable_continuous_comp_compact ν _ (hθ θ).measurable F hF
  have hgLip (θ φ : Fin K → ℝ) :
      |g θ - g φ| ≤ (L * Real.sqrt n) * Real.sqrt (∑ i, (θ i - φ i) ^ 2) := by
    apply abs_integral_sections_sub_le ν (fun θ U => f (θ, U)) θ φ (hfi θ) (hfi φ)
    apply Filter.Eventually.of_forall
    intro U
    calc
      _ ≤ L * unitaryProductFrobeniusDist (phaseCubeMultiply θ U) (phaseCubeMultiply φ U) := hLip _ _
      _ ≤ L * (Real.sqrt n * Real.sqrt (∑ i, (θ i - φ i) ^ 2)) :=
        mul_le_mul_of_nonneg_left (phaseCubeMultiply_phase_distance_le θ φ U) hL
      _ = _ := by ring
  have hsection : ∀ᵐ θ ∂μ, Real.log (∫ U, Real.exp (f (θ, U)) ∂ν) ≤
      g θ + cSU * L ^ 2 / n := by
    apply Filter.Eventually.of_forall
    intro θ
    apply hSU _ (hF.comp (hθ θ)) L hL
    intro U V
    simpa only [phaseCubeMultiply_distance, Function.comp_def] using
      hLip (phaseCubeMultiply θ U) (phaseCubeMultiply θ V)
  obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  have hgBound (θ : Fin K → ℝ) : |g θ| ≤ R := by
    have h := norm_integral_le_of_norm_le_const (μ := ν) (f := fun U => f (θ, U))
      (Filter.Eventually.of_forall fun U => hR (phaseCubeMultiply θ U) (Set.mem_univ _))
    simpa only [probReal_univ, mul_one, Real.norm_eq_abs] using h
  have heg : Integrable (fun θ => Real.exp (g θ)) μ := by
    apply Integrable.of_bound (Real.continuous_exp.comp hg).aestronglyMeasurable (Real.exp R)
    apply Filter.Eventually.of_forall
    intro θ
    rw [Real.norm_eq_abs, Function.comp_def, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hgBound θ))
  have hmean := hPhase g hg (L * Real.sqrt n) (mul_nonneg hL (Real.sqrt_nonneg n)) hgLip
  have hcost : cPhase / (n : ℝ) ^ 2 * (L * Real.sqrt n) ^ 2 = cPhase * L ^ 2 / n := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    field_simp
  rw [hcost] at hmean
  have h := logmean_prod_le_of_logmean_sections μ ν f hi hei heg
    (cSU * L ^ 2 / n) (cPhase * L ^ 2 / n) hsection hmean
  have hIntegral (G : (Fin K → Matrix.unitaryGroup (Fin n) ℂ) → ℝ) (hG : Continuous G) :
      (∫ p, G (phaseCubeMultiply p.1 p.2) ∂μ.prod ν) =
        ∫ U, G U ∂Measure.pi (fun _ : Fin K => unitaryHaar n) := by
    rw [← hmap]
    exact (integral_map hp.aemeasurable hG.measurable.aestronglyMeasurable).symm
  dsimp only [f] at h
  rw [hIntegral (fun U => Real.exp (F U)) (Real.continuous_exp.comp hF), hIntegral F hF] at h
  convert h using 1 <;> ring

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ProductChernoff -/
section
open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 800000

theorem continuous_of_unitaryProductFrobenius_lipschitz {n K : ℕ}
    (F : (Fin K → Matrix.unitaryGroup (Fin n) ℂ) → ℝ) (L : ℝ)
    (hLip : ∀ U V, |F U - F V| ≤ L * unitaryProductFrobeniusDist U V) : Continuous F := by
  apply continuous_iff_continuousAt.mpr
  intro U
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hc : Continuous (fun V => L * unitaryProductFrobeniusDist V U) := by
    simp_rw [unitaryProductFrobeniusDist_eq_entry]
    have he (i : Fin K) (x y : Fin n) :
        Continuous (fun V : Fin K → Matrix.unitaryGroup (Fin n) ℂ =>
          (V i : Matrix (Fin n) (Fin n) ℂ) x y) := by
      have hi : Continuous (fun V : Fin K → Matrix.unitaryGroup (Fin n) ℂ => V i) :=
        continuous_apply i
      have hu : Continuous (fun W : Matrix.unitaryGroup (Fin n) ℂ =>
          (W : Matrix (Fin n) (Fin n) ℂ)) := continuous_subtype_val
      have hentry : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => A x y) :=
        (continuous_apply y).comp (continuous_apply x)
      exact hentry.comp (hu.comp hi)
    apply Continuous.mul continuous_const
    apply Real.continuous_sqrt.comp
    apply continuous_finset_sum
    intro i hi
    apply continuous_finset_sum
    intro x hx
    apply continuous_finset_sum
    intro y hy
    exact ((he i x y).sub continuous_const).norm.pow 2
  have hlim : Filter.Tendsto (fun V => L * unitaryProductFrobeniusDist V U)
      (nhds U) (nhds 0) := by
    simpa only [unitaryProductFrobeniusDist_eq_entry, sub_self, norm_zero, zero_pow (by omega : 2 ≠ 0),
      Finset.sum_const_zero, Real.sqrt_zero, mul_zero] using
        (hc.continuousAt (x := U)).tendsto
  exact squeeze_zero (fun V => dist_nonneg) (fun V => by
    simpa only [Real.dist_eq] using hLip V U) hlim

/-- A dimension-scaled log-mean bound supplies a centered sub-Gaussian MGF. -/
theorem unitary_product_subgaussian_of_logmean {n K : ℕ} (hn : 1 ≤ n)
    (ν : Measure (Fin K → Matrix.unitaryGroup (Fin n) ℂ)) [IsProbabilityMeasure ν]
    (c : ℝ) (hc : 0 ≤ c) (hmean : UnitaryProductLogMeanBound n K ν c)
    (F : (Fin K → Matrix.unitaryGroup (Fin n) ℂ) → ℝ) (hF : Continuous F)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ U V, |F U - F V| ≤ L * unitaryProductFrobeniusDist U V) :
    HasSubgaussianMGF (fun U => F U - ∫ V, F V ∂ν)
      ⟨2 * c * L ^ 2 / n, by positivity⟩ ν := by
  letI : SecondCountableTopology (Matrix.unitaryGroup (Fin n) ℂ) := inferInstance
  let m := ∫ V, F V ∂ν
  have hFi := integrable_continuous_comp_compact ν id measurable_id F hF
  change Integrable F ν at hFi
  have hcont (t : ℝ) : Continuous (fun U => t * (F U - m)) :=
    (hF.sub continuous_const).const_mul t
  have hexp (t : ℝ) : Integrable (fun U => Real.exp (t * (F U - m))) ν :=
    integrable_continuous_comp_compact ν id measurable_id _ (Real.continuous_exp.comp (hcont t))
  refine ⟨hexp, ?_⟩
  intro t
  have h := hmean (fun U => t * (F U - m)) (hcont t) (|t| * L)
    (mul_nonneg (abs_nonneg t) hL) (by
      intro U V
      rw [← mul_sub, sub_sub_sub_cancel_right, abs_mul]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hLip U V) (abs_nonneg t))
  have hint : (∫ U, t * (F U - m) ∂ν) = 0 := by
    rw [integral_const_mul, integral_sub hFi (integrable_const m)]
    simp [m]
  rw [hint, zero_add] at h
  have hcoef : c * (|t| * L) ^ 2 / n = (2 * c * L ^ 2 / n) * t ^ 2 / 2 := by
    rw [mul_pow, sq_abs]
    ring
  rw [hcoef] at h
  exact (Real.log_le_iff_le_exp (integral_exp_pos (hexp t))).mp h

/-- The two-sided Chernoff consequence, with no dependence on the number of factors. -/
theorem unitary_product_tail_of_logmean {n K : ℕ} (hn : 1 ≤ n)
    (ν : Measure (Fin K → Matrix.unitaryGroup (Fin n) ℂ)) [IsProbabilityMeasure ν]
    (c : ℝ) (hc : 0 < c) (hmean : UnitaryProductLogMeanBound n K ν c)
    (F : (Fin K → Matrix.unitaryGroup (Fin n) ℂ) → ℝ) (hF : Continuous F)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V, |F U - F V| ≤ L * unitaryProductFrobeniusDist U V)
    (u : ℝ) (hu : 0 ≤ u) :
    ν {U | u ≤ |F U - ∫ V, F V ∂ν|} ≤
      ENNReal.ofReal (2 * Real.exp (-((n : ℝ) * u ^ 2) / (4 * c * L ^ 2))) := by
  let X := fun U => F U - ∫ V, F V ∂ν
  have hsg := unitary_product_subgaussian_of_logmean hn ν c hc.le hmean F hF L hL.le hLip
  have hp := hsg.measure_ge_le hu
  have hm := hsg.neg.measure_ge_le hu
  change ν.real {U | u ≤ F U - ∫ V, F V ∂ν} ≤
    Real.exp (-u ^ 2 / (2 * (2 * c * L ^ 2 / n))) at hp
  change ν.real {U | u ≤ -(F U - ∫ V, F V ∂ν)} ≤
    Real.exp (-u ^ 2 / (2 * (2 * c * L ^ 2 / n))) at hm
  have hset : {U | u ≤ |X U|} = {U | u ≤ X U} ∪ {U | u ≤ -X U} := by
    ext U
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs]
  have hreal : ν.real {U | u ≤ |X U|} ≤
      2 * Real.exp (-u ^ 2 / (2 * (2 * c * L ^ 2 / n))) := by
    rw [hset]
    have h := measureReal_union_le (μ := ν) {U | u ≤ X U} {U | u ≤ -X U}
    dsimp only [X] at h ⊢
    linarith
  have heq : -u ^ 2 / (2 * (2 * c * L ^ 2 / n)) =
      -((n : ℝ) * u ^ 2) / (4 * c * L ^ 2) := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
    <;> ring
  rw [heq] at hreal
  calc
    _ = ENNReal.ofReal (ν.real {U | u ≤ |X U|}) :=
      (ENNReal.ofReal_toReal (measure_ne_top ν _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- The actual numerical tail in SpectrumLB Eq. (7.14) follows from the product
log-mean constant `1+π`, supplied by SU concentration and Gaussian phase transport. -/
theorem spectrum_tail_of_unitary_product_logmean (n K : ℕ)
    (hmean : UnitaryProductLogMeanBound n K
      (Measure.pi (fun _ : Fin K => unitaryHaar n)) (1 + Real.pi))
    (L : ℝ) (hL : 0 < L)
    (F : (Fin K → Matrix.unitaryGroup (Fin n) ℂ) → ℝ)
    (hLip : ∀ U V : Fin K → Matrix.unitaryGroup (Fin n) ℂ,
      |F U - F V| ≤ L * Real.sqrt (∑ i, ∑ x, ∑ y,
        ‖(U i : Matrix (Fin n) (Fin n) ℂ) x y -
          (V i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2))
    (u : ℝ) (hu : 0 ≤ u) :
    SpectrumLB.haarK n K {U | u ≤ |F U - ∫ V, F V ∂SpectrumLB.haarK n K|} ≤
      ENNReal.ofReal (2 * Real.exp (-(((n : ℝ) - 2) * u ^ 2) / (24 * L ^ 2))) := by
  letI : IsProbabilityMeasure (SpectrumLB.haarK n K) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin K => unitaryHaar n))
    infer_instance
  by_cases hn : n ≤ 2
  · have hn2 : (n : ℝ) ≤ 2 := by exact_mod_cast hn
    have hexp : 1 ≤ Real.exp (-(((n : ℝ) - 2) * u ^ 2) / (24 * L ^ 2)) := by
      apply Real.one_le_exp_iff.mpr
      apply div_nonneg _ (by positivity)
      exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg u))
    calc
      _ ≤ SpectrumLB.haarK n K Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ ≤ _ := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by linarith)
  · have hn1 : 1 ≤ n := by omega
    have hLip' : ∀ U V, |F U - F V| ≤ L * unitaryProductFrobeniusDist U V := by
      simpa only [unitaryProductFrobeniusDist_eq_entry] using hLip
    have ht := unitary_product_tail_of_logmean hn1 (SpectrumLB.haarK n K)
      (1 + Real.pi) (by positivity) hmean F
      (continuous_of_unitaryProductFrobenius_lipschitz F L hLip') L hL hLip' u hu
    apply ht.trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    apply neg_le_neg
    calc
      ((n : ℝ) - 2) * u ^ 2 / (24 * L ^ 2) ≤ (n : ℝ) * u ^ 2 / (24 * L ^ 2) := by
        gcongr
        linarith
      _ ≤ (n : ℝ) * u ^ 2 / (4 * (1 + Real.pi) * L ^ 2) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        have hp := Real.pi_lt_four
        exact mul_le_mul_of_nonneg_right (by linarith : 4 * (1 + Real.pi) ≤ 24) (sq_nonneg L)

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ProductPhaseLaw -/
section
open MeasureTheory

namespace BosonicLearn.Prop2
noncomputable section

/-- A scalar pushforward identity tensorizes after grouping the two independent
families of coordinates. This is the measure identity needed by the phase-cube reduction. -/
theorem map_prod_pi_coordinate_pair {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (f : A × B → C) (hf : Measurable f) (hmap : (μ.prod ν).map f = ρ) (K : ℕ) :
    ((Measure.pi (fun _ : Fin K => μ)).prod (Measure.pi (fun _ : Fin K => ν))).map
      (fun p i => f (p.1 i, p.2 i)) = Measure.pi (fun _ : Fin K => ρ) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow A B (Fin K)
  have he := measurePreserving_arrowProdEquivProdArrow A B (Fin K) (fun _ => μ) (fun _ => ν)
  have hg : Measurable (fun p : (Fin K → A) × (Fin K → B) => fun i => f (p.1 i, p.2 i)) := by
    apply measurable_pi_lambda
    intro i
    exact hf.comp (((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  rw [← he.map_eq, Measure.map_map hg e.measurable]
  change (Measure.pi (fun _ : Fin K => μ.prod ν)).map (fun x i => f (x i)) = _
  have : IsProbabilityMeasure ((μ.prod ν).map f) := by rw [hmap]; infer_instance
  rw [Measure.pi_map_pi (fun _ => hf.aemeasurable)]
  simp only [hmap]

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2GaussianCDF -/
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace BosonicLearn.Prop2
noncomputable section

/-- The standard normal cumulative distribution function. -/
def standardGaussianCDF : ℝ → ℝ := cdf (gaussianReal 0 1)

/-- The maximum density of the standard real Gaussian. -/
def standardGaussianDensityBound : ℝ := 1 / Real.sqrt (2 * Real.pi)

theorem standardGaussianDensityBound_pos : 0 < standardGaussianDensityBound := by
  unfold standardGaussianDensityBound
  positivity

theorem gaussianPDFReal_standard_le (x : ℝ) :
    gaussianPDFReal 0 1 x ≤ standardGaussianDensityBound := by
  unfold gaussianPDFReal standardGaussianDensityBound
  norm_num only [NNReal.coe_one, mul_one, sub_zero]
  have h : Real.exp (-x^2 / (2:ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) (by norm_num))
  have hm := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Real.sqrt_nonneg (2*Real.pi)))
  simpa [one_div] using hm

theorem standardGaussianCDF_sub_nonneg {x y : ℝ} (hxy : x ≤ y) :
    0 ≤ standardGaussianCDF y - standardGaussianCDF x :=
  sub_nonneg.mpr (monotone_cdf _ hxy)

theorem standardGaussianCDF_measure_Ioc (x y : ℝ) :
    gaussianReal 0 1 (Ioc x y) =
      ENNReal.ofReal (standardGaussianCDF y - standardGaussianCDF x) := by
  rw [← measure_cdf (gaussianReal 0 1), StieltjesFunction.measure_Ioc]
  rfl

/-- Gaussian interval probabilities are bounded by maximum density times length. -/
theorem standardGaussianCDF_sub_le {x y : ℝ} (hxy : x ≤ y) :
    standardGaussianCDF y - standardGaussianCDF x ≤
      standardGaussianDensityBound * (y-x) := by
  have h : gaussianReal 0 1 (Ioc x y) ≤
      ENNReal.ofReal standardGaussianDensityBound * volume (Ioc x y) := by
    rw [gaussianReal_apply 0 (by norm_num)]
    calc
      _ ≤ ∫⁻ _ in Ioc x y, ENNReal.ofReal standardGaussianDensityBound := by
        apply lintegral_mono
        intro z
        exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_standard_le z)
      _ = _ := by simp
  rw [standardGaussianCDF_measure_Ioc, Real.volume_Ioc,
    ← ENNReal.ofReal_mul standardGaussianDensityBound_pos.le] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg standardGaussianDensityBound_pos.le (sub_nonneg.mpr hxy))).mp h

/-- The Gaussian CDF has the sharp global Lipschitz constant `1/sqrt(2π)`. -/
theorem standardGaussianCDF_abs_sub_le (x y : ℝ) :
    |standardGaussianCDF x - standardGaussianCDF y| ≤
      standardGaussianDensityBound * |x-y| := by
  rcases le_total x y with h | h
  · rw [abs_sub_comm, abs_of_nonneg (standardGaussianCDF_sub_nonneg h),
      abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr h)]
    exact standardGaussianCDF_sub_le h
  · rw [abs_of_nonneg (standardGaussianCDF_sub_nonneg h),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact standardGaussianCDF_sub_le h

theorem lipschitzWith_standardGaussianCDF :
    LipschitzWith ⟨standardGaussianDensityBound, standardGaussianDensityBound_pos.le⟩
      standardGaussianCDF := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |standardGaussianCDF x - standardGaussianCDF y| ≤
    standardGaussianDensityBound * |x-y|
  exact standardGaussianCDF_abs_sub_le x y

theorem continuous_standardGaussianCDF : Continuous standardGaussianCDF :=
  lipschitzWith_standardGaussianCDF.continuous

theorem strictMono_standardGaussianCDF : StrictMono standardGaussianCDF := by
  intro x y hxy
  have hn : gaussianReal 0 1 (Ioc x y) ≠ 0 := by
    intro hz
    have hv := gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : ℝ≥0) ≠ 0) hz
    rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at hv
    linarith
  rw [standardGaussianCDF_measure_Ioc, Ne, ENNReal.ofReal_eq_zero] at hn
  linarith

theorem standardGaussianCDF_mem_Ioo (x : ℝ) : standardGaussianCDF x ∈ Ioo (0:ℝ) 1 := by
  constructor
  · exact (cdf_nonneg _ (x-1)).trans_lt (strictMono_standardGaussianCDF (by linarith))
  · exact (strictMono_standardGaussianCDF (show x < x+1 by linarith)).trans_le
      (cdf_le_one _ (x+1))

theorem standardGaussianCDF_surj_Ioo {y : ℝ} (hy : y ∈ Ioo (0:ℝ) 1) :
    ∃ x, standardGaussianCDF x = y := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot (gaussianReal 0 1)).eventually_lt_const hy.1).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop (gaussianReal 0 1)).eventually_const_lt hy.2).exists
  exact intermediate_value_univ a b continuous_standardGaussianCDF ⟨ha.le, hb.le⟩

/-- The probability integral transform for the standard Gaussian. -/
theorem map_standardGaussianCDF :
    (gaussianReal 0 1).map standardGaussianCDF = volume.restrict (Icc (0:ℝ) 1) := by
  apply Measure.ext_of_Iic
  intro y
  rw [Measure.map_apply continuous_standardGaussianCDF.measurable measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic]
  by_cases hy0 : y ≤ 0
  · have hempty : standardGaussianCDF ⁻¹' Iic y = ∅ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact not_le.mpr (hy0.trans_lt (standardGaussianCDF_mem_Ioo x).1)
    rw [hempty, measure_empty]
    have hi : Iic y ∩ Icc (0:ℝ) 1 ⊆ {0} := by
      intro x hx
      simp only [mem_inter_iff, mem_Iic, mem_Icc] at hx
      simp only [mem_singleton_iff]
      linarith
    exact (measure_mono_null hi (measure_singleton 0)).symm
  · by_cases hy1 : 1 ≤ y
    · have hall : standardGaussianCDF ⁻¹' Iic y = univ := by
        ext x
        simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
        exact (standardGaussianCDF_mem_Ioo x).2.le.trans hy1
      rw [hall, measure_univ]
      have hi : Iic y ∩ Icc (0:ℝ) 1 = Icc 0 1 := by
        apply inter_eq_right.mpr
        intro x hx
        exact hx.2.trans hy1
      rw [hi, Real.volume_Icc]
      norm_num
    · obtain ⟨x, hx⟩ := standardGaussianCDF_surj_Ioo ⟨lt_of_not_ge hy0, lt_of_not_ge hy1⟩
      have hi : standardGaussianCDF ⁻¹' Iic y = Iic x := by
        ext z
        simp only [mem_preimage, mem_Iic, ← hx, strictMono_standardGaussianCDF.le_iff_le]
      rw [hi, ← ofReal_cdf (gaussianReal 0 1) x]
      change ENNReal.ofReal (standardGaussianCDF x) = _
      rw [hx]
      have hs : Iic y ∩ Icc (0:ℝ) 1 = Icc 0 y := by
        ext z
        simp only [mem_inter_iff, mem_Iic, mem_Icc]
        constructor
        · exact fun h => ⟨h.2.1,h.1⟩
        · exact fun h => ⟨h.2,h.1,h.2.trans (le_of_not_ge hy1)⟩
      rw [hs, Real.volume_Icc, sub_zero]


/-- The affine Gaussian CDF transports Gaussian measure to normalized Lebesgue
measure on an interval of length `ell`. -/
theorem map_scaled_standardGaussianCDF (ell : ℝ) (hell : 0 < ell) :
    (gaussianReal 0 1).map (fun x => ell * standardGaussianCDF x) =
      ENNReal.ofReal ell⁻¹ • volume.restrict (Icc (0:ℝ) ell) := by
  have hcomp : (fun x => ell * standardGaussianCDF x) =
      (fun x => ell*x) ∘ standardGaussianCDF := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) continuous_standardGaussianCDF.measurable,
    map_standardGaussianCDF]
  have hemb : MeasurableEmbedding (fun x : ℝ => ell*x) :=
    (Homeomorph.mulLeft₀ ell hell.ne').measurableEmbedding
  have hr := hemb.restrict_map (volume : Measure ℝ) (Icc 0 ell)
  rw [preimage_const_mul_Icc₀ 0 ell hell, zero_div, div_self hell.ne'] at hr
  rw [← hr, Real.map_volume_mul_left hell.ne', Measure.restrict_smul]
  rw [abs_of_pos (inv_pos.mpr hell)]

/-- The scaled transform stays in the defining interval pointwise. -/
theorem scaled_standardGaussianCDF_mem_Icc (ell : ℝ) (hell : 0 ≤ ell) (x : ℝ) :
    ell * standardGaussianCDF x ∈ Icc (0:ℝ) ell := by
  constructor
  · exact mul_nonneg hell (cdf_nonneg _ _)
  · calc
      _ ≤ ell*1 := mul_le_mul_of_nonneg_left (cdf_le_one _ _) hell
      _ = ell := mul_one ell

/-- The Gaussian-to-uniform transform acts independently on any finite number
of coordinates. -/
theorem map_pi_scaled_standardGaussianCDF {ι : Type*} [Fintype ι]
    (ell : ℝ) (hell : 0 < ell) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map
      (fun x i => ell * standardGaussianCDF (x i)) =
      Measure.pi (fun _ : ι => ENNReal.ofReal ell⁻¹ • volume.restrict (Icc (0:ℝ) ell)) := by
  rw [Measure.pi_map_pi (f := fun _ x => ell * standardGaussianCDF x)
    (fun _ => (measurable_const.mul continuous_standardGaussianCDF.measurable).aemeasurable)]
  simp_rw [map_scaled_standardGaussianCDF ell hell]

/-- Coordinatewise scalar Lipschitz bounds preserve the Euclidean constant. -/
theorem euclidean_scaled_standardGaussianCDF_lipschitz {ι : Type*} [Fintype ι]
    (ell : ℝ) (hell : 0 ≤ ell) (x y : ι → ℝ) :
    Real.sqrt (∑ i, (ell * standardGaussianCDF (x i) -
      ell * standardGaussianCDF (y i))^2) ≤
      (ell * standardGaussianDensityBound) * Real.sqrt (∑ i, (x i-y i)^2) := by
  have hcoord (i : ι) : (ell * standardGaussianCDF (x i) -
      ell * standardGaussianCDF (y i))^2 ≤
      (ell * standardGaussianDensityBound)^2 * (x i-y i)^2 := by
    have h := mul_le_mul_of_nonneg_left (standardGaussianCDF_abs_sub_le (x i) (y i)) hell
    have habs : |ell * (standardGaussianCDF (x i) - standardGaussianCDF (y i))| ≤
        ell * (standardGaussianDensityBound * |x i-y i|) := by
      simpa only [abs_mul, abs_of_nonneg hell] using h
    have hnonneg : 0 ≤ ell * (standardGaussianDensityBound * |x i-y i|) := by
      exact mul_nonneg hell (mul_nonneg standardGaussianDensityBound_pos.le (abs_nonneg _))
    have hs := sq_le_sq₀ (abs_nonneg (ell * (standardGaussianCDF (x i) - standardGaussianCDF (y i)))) hnonneg |>.mpr habs
    rw [sq_abs] at hs
    simpa only [mul_sub, mul_pow, sq_abs, mul_assoc] using hs
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcoord i)
  rw [← Finset.mul_sum] at hs
  calc
    _ ≤ Real.sqrt ((ell * standardGaussianDensityBound)^2 * ∑ i, (x i-y i)^2) :=
      Real.sqrt_le_sqrt hs
    _ = _ := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hell standardGaussianDensityBound_pos.le)]

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2GaussianCube -/
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace BosonicLearn.Prop2
noncomputable section

/-- A normalized interval, represented as a Gaussian CDF pushforward. -/
def uniformIntervalLaw (ell : ℝ) : Measure ℝ :=
  ENNReal.ofReal ell⁻¹ • volume.restrict (Icc (0:ℝ) ell)

theorem isProbabilityMeasure_uniformIntervalLaw (ell : ℝ) (hell : 0 < ell) :
    IsProbabilityMeasure (uniformIntervalLaw ell) := by
  unfold uniformIntervalLaw
  rw [← map_scaled_standardGaussianCDF ell hell]
  exact Measure.isProbabilityMeasure_map
    (measurable_const.mul continuous_standardGaussianCDF.measurable).aemeasurable

/-- Uniform measure on a cube satisfies a dimension-independent log-exponential
mean bound. The Gaussian CDF transport gives the constant `ell²/(4π)`. -/
theorem uniform_cube_logmean {ι : Type*} [Fintype ι]
    (ell : ℝ) (hell : 0 < ell) (F : (ι → ℝ) → ℝ) (hF : Continuous F)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y, |F x-F y| ≤ L * Real.sqrt (∑ i, (x i-y i)^2)) :
    Real.log (∫ x, Real.exp (F x) ∂Measure.pi (fun _ : ι => uniformIntervalLaw ell)) ≤
      (∫ x, F x ∂Measure.pi (fun _ : ι => uniformIntervalLaw ell)) + ell^2*L^2/(4*Real.pi) := by
  let μ : Measure (ι → ℝ) := Measure.pi (fun _ : ι => gaussianReal 0 1)
  let T : (ι → ℝ) → (ι → ℝ) := fun x i => ell * standardGaussianCDF (x i)
  have hT : Continuous T := by
    apply continuous_pi
    intro i
    exact continuous_const.mul (continuous_standardGaussianCDF.comp (continuous_apply i))
  have hmap : μ.map T = Measure.pi (fun _ : ι => uniformIntervalLaw ell) :=
    map_pi_scaled_standardGaussianCDF ell hell
  have hcompact : IsCompact {x : ι → ℝ | ∀ i, x i ∈ Icc (0:ℝ) ell} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  obtain ⟨R,hR⟩ := hcompact.bddAbove_image hF.norm.continuousOn
  have hb (x : ι → ℝ) : ‖F (T x)‖ ≤ R := by
    apply hR
    exact ⟨T x, fun i => scaled_standardGaussianCDF_mem_Icc ell hell.le (x i), rfl⟩
  have hint (t : ℝ) : Integrable (fun x => Real.exp (t * F (T x))) μ := by
    apply Integrable.of_bound (((hF.comp hT).const_mul t).rexp.aestronglyMeasurable)
      (Real.exp (|t| * R))
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      t * F (T x) ≤ |t * F (T x)| := le_abs_self _
      _ = |t| * ‖F (T x)‖ := by rw [abs_mul, Real.norm_eq_abs]
      _ ≤ |t| * R := mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)
  have hcompLip (x y : ι → ℝ) :
      |F (T x)-F (T y)| ≤ (L * (ell * standardGaussianDensityBound)) *
        Real.sqrt (∑ i, (x i-y i)^2) := by
    calc
      _ ≤ L * Real.sqrt (∑ i, ((T x) i-(T y) i)^2) := hLip _ _
      _ ≤ L * ((ell * standardGaussianDensityBound) * Real.sqrt (∑ i, (x i-y i)^2)) :=
        mul_le_mul_of_nonneg_left
          (euclidean_scaled_standardGaussianCDF_lipschitz ell hell.le x y) hL
      _ = _ := by ring
  have h := Prop5.logmean_le_mean_add_of_entropy μ (fun x => F (T x))
    ((L * (ell * standardGaussianDensityBound))^2/2) hint (by
      intro t ht
      have he := GaussianMatrix.gaussian_lipschitz_entropy_bound
        (fun x => F (T x)) (L * (ell * standardGaussianDensityBound)) hcompLip t
      convert he using 1 <;> ring)
  have hc : (L * (ell * standardGaussianDensityBound))^2/2 = ell^2*L^2/(4*Real.pi) := by
    unfold standardGaussianDensityBound
    have hs := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
    have hp := Real.pi_pos
    have hroot : Real.sqrt (2*Real.pi) ≠ 0 := by positivity
    field_simp
    nlinarith
  rw [hc] at h
  rw [← hmap, integral_map hT.aemeasurable hF.rexp.aestronglyMeasurable,
    integral_map hT.aemeasurable hF.aestronglyMeasurable]
  exact h

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2ShortPhaseCube -/
section
open MeasureTheory Set
open scoped ENNReal

namespace BosonicLearn.Prop2
noncomputable section

theorem shortPhaseLaw_eq_uniformIntervalLaw (n : ℕ) (hn : 1 ≤ n) :
    shortPhaseLaw n = uniformIntervalLaw (2 * Real.pi / n) := by
  have hell : 0 < 2 * Real.pi / n := by positivity
  rw [shortPhaseLaw, uniformIntervalLaw, ENNReal.ofReal_inv_of_pos hell,
    restrict_Ico_eq_restrict_Icc]

/-- Short independent scalar phases satisfy a Euclidean logmean bound with
constant `π/n²`, uniformly in the number of phases. -/
theorem short_phase_cube_logmean (n K : ℕ) (hn : 1 ≤ n) :
    EuclideanLogMeanBound K (Measure.pi (fun _ : Fin K => shortPhaseLaw n))
      (Real.pi / (n : ℝ)^2) := by
  intro F hF L hL hLip
  simp_rw [shortPhaseLaw_eq_uniformIntervalLaw n hn]
  have hell : 0 < 2 * Real.pi / n := by positivity
  have h := uniform_cube_logmean (2 * Real.pi / n) hell F hF L hL hLip
  have hc : (2 * Real.pi / (n:ℝ))^2 * L^2 / (4 * Real.pi) =
      (Real.pi / (n:ℝ)^2) * L^2 := by
    have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
    field_simp
    ring
  rw [hc] at h
  exact h

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2SpectrumFromSpecialUnitary -/
section
open MeasureTheory
open scoped Matrix ENNReal Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 800000

/-- Meckes' exact scalar factorization holds simultaneously in every independent coordinate. -/
theorem shortPhase_unitary_product_map (n K : ℕ) (hn : 1 ≤ n) :
    ((Measure.pi (fun _ : Fin K => shortPhaseLaw n)).prod
      (Measure.pi (fun _ : Fin K => specialUnitaryHaarOnUnitary n))).map
      (fun p => phaseCubeMultiply p.1 p.2) = Measure.pi (fun _ : Fin K => unitaryHaar n) := by
  letI : IsProbabilityMeasure (shortPhaseLaw n) := shortPhaseLaw_probability hn
  exact map_prod_pi_coordinate_pair (shortPhaseLaw n) (specialUnitaryHaarOnUnitary n)
    (unitaryHaar n) (fun p => phaseMultiply p.1 p.2) (continuous_phaseMultiply n).measurable
    (shortPhase_unitary_map hn) K

/-- The entire unitary-group concentration problem reduces to the special-unitary
product log-mean bound. Gaussian transport handles every scalar phase at once. -/
theorem unitary_product_logmean_of_specialUnitary (n K : ℕ) (hn : 1 ≤ n)
    (hSU : UnitaryProductLogMeanBound n K
      (Measure.pi (fun _ : Fin K => specialUnitaryHaarOnUnitary n)) 1) :
    UnitaryProductLogMeanBound n K (Measure.pi (fun _ : Fin K => unitaryHaar n))
      (1 + Real.pi) := by
  letI : IsProbabilityMeasure (shortPhaseLaw n) := shortPhaseLaw_probability hn
  exact unitary_product_logmean_of_phase_factorization n K hn
    (Measure.pi (fun _ : Fin K => shortPhaseLaw n))
    (Measure.pi (fun _ : Fin K => specialUnitaryHaarOnUnitary n))
    (shortPhase_unitary_product_map n K hn) 1 Real.pi hSU (short_phase_cube_logmean n K hn)

theorem unitary_product_logmean_zero_dimension (K : ℕ) (c : ℝ) :
    UnitaryProductLogMeanBound 0 K (Measure.pi (fun _ : Fin K => unitaryHaar 0)) c := by
  intro F hF L hL hLip
  have hval (U : Fin K → Matrix.unitaryGroup (Fin 0) ℂ) : F U = F (fun _ => 1) :=
    congrArg F (Subsingleton.elim _ _)
  simp only [hval, integral_const, probReal_univ, one_smul, Nat.cast_zero, div_zero,
    add_zero, Real.log_exp, le_refl]

/-- The exact pre-existing SpectrumLB concentration statement, conditional only
on the Riemannian/heat-flow log-mean bound on SU(n)^K. No unitary Haar concentration
theorem is imported or used in this reduction. -/
theorem spectrum_eq_7_14_of_specialUnitary_logmean
    (hSU : ∀ n K : ℕ, 1 ≤ n → UnitaryProductLogMeanBound n K
      (Measure.pi (fun _ : Fin K => specialUnitaryHaarOnUnitary n)) 1)
    (n K : ℕ) (L : ℝ) (hL : 0 < L)
    (F : (Fin K → Matrix.unitaryGroup (Fin n) ℂ) → ℝ)
    (hLip : ∀ U V : Fin K → Matrix.unitaryGroup (Fin n) ℂ,
      |F U - F V| ≤ L * Real.sqrt (∑ i, ∑ x, ∑ y,
        ‖(U i : Matrix (Fin n) (Fin n) ℂ) x y -
          (V i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2))
    (u : ℝ) (hu : 0 ≤ u) :
    SpectrumLB.haarK n K {U | u ≤ |F U - ∫ V, F V ∂SpectrumLB.haarK n K|} ≤
      ENNReal.ofReal (2 * Real.exp (-(((n : ℝ) - 2) * u ^ 2) / (24 * L ^ 2))) := by
  apply spectrum_tail_of_unitary_product_logmean n K _ L hL F hLip u hu
  by_cases hn : n = 0
  · subst n
    exact unitary_product_logmean_zero_dimension K (1 + Real.pi)
  · exact unitary_product_logmean_of_specialUnitary n K (by omega) (hSU n K (by omega))

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2SpecialUnitaryReduction -/
section
open MeasureTheory
open scoped Matrix ENNReal Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 800000

/-- Restrict an ambient function to actual determinant-one unitaries and transport
the product Haar law through the inclusion. This isolates the standard SU theorem
from all definitions used by the unitary concentration reduction. -/
theorem special_unitary_product_logmean_pushforward (n K : ℕ)
    (hSU : ∀ (F : (Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ) → ℝ),
      Continuous F → ∀ L : ℝ, 0 ≤ L →
      (∀ U V : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ,
        |F U - F V| ≤ L * Real.sqrt (∑ i, ∑ x, ∑ y,
          ‖(U i : Matrix (Fin n) (Fin n) ℂ) x y -
            (V i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2)) →
      Real.log (∫ U, Real.exp (F U) ∂Measure.pi (fun _ : Fin K => specialUnitaryHaar n)) -
        L ^ 2 / n ≤ ∫ U, F U ∂Measure.pi (fun _ : Fin K => specialUnitaryHaar n)) :
    UnitaryProductLogMeanBound n K
      (Measure.pi (fun _ : Fin K => specialUnitaryHaarOnUnitary n)) 1 := by
  letI : SecondCountableTopology (Matrix.unitaryGroup (Fin n) ℂ) := inferInstance
  letI : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin n) ℂ) := inferInstance
  let f : (Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ) →
      (Fin K → Matrix.unitaryGroup (Fin n) ℂ) := fun U i => specialUnitaryInclusion n (U i)
  have hf : Continuous f := continuous_pi fun i =>
    (continuous_specialUnitaryInclusion n).comp (continuous_apply i)
  have hmap : (Measure.pi (fun _ : Fin K => specialUnitaryHaar n)).map f =
      Measure.pi (fun _ : Fin K => specialUnitaryHaarOnUnitary n) := by
    exact Measure.pi_map_pi (fun _ => (continuous_specialUnitaryInclusion n).measurable.aemeasurable)
  intro F hF L hL hLip
  have h := hSU (F ∘ f) (hF.comp hf) L hL (by
    intro U V
    have hh := hLip (f U) (f V)
    rw [unitaryProductFrobeniusDist_eq_entry] at hh
    exact hh)
  rw [← hmap, integral_map hf.measurable.aemeasurable hF.rexp.aestronglyMeasurable,
    integral_map hf.measurable.aemeasurable hF.aestronglyMeasurable]
  simpa only [one_mul, Function.comp_apply] using (sub_le_iff_le_add.mp h)

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2SpectrumFromPolynomialLSI -/
section
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section

/-- The exact Spectrum concentration target follows from positive polynomial
density logarithmic Sobolev on SU(n)^K. This wrapper includes uniform polynomial
approximation, entropy continuity, Herbst, SU-to-U Haar transport, Gaussian
transport of the phase cube, and the two-sided Chernoff bound. It imports neither
the target concentration theorem nor the unposted special-unitary draft. -/
theorem spectrum_eq_7_14_of_polynomial_logSobolev
    (hpoly : ∀ (n K : ℕ), 1 ≤ n → ∀ (d : ℕ)
      (p : C(Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ, ℝ)),
      p ∈ specialUnitaryProductPolynomialSpace n K d →
      (∀ U, 0 < p U) → ∀ (L : ℝ), 0 ≤ L →
      (∀ U V : Fin K → Matrix.specialUnitaryGroup (Fin n) ℂ,
        |Real.log (p U) - Real.log (p V)| ≤ L * Real.sqrt
          (∑ i, ∑ x, ∑ y, ‖(U i : Matrix (Fin n) (Fin n) ℂ) x y -
            (V i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2)) →
      continuousDensityEntropy (Measure.pi (fun _ : Fin K => specialUnitaryHaar n)) p ≤
        L^2 / n * ∫ U, p U ∂(Measure.pi (fun _ : Fin K => specialUnitaryHaar n)))
    (n K : ℕ) (L : ℝ) (hL : 0 < L)
    (F : (Fin K → Matrix.unitaryGroup (Fin n) ℂ) → ℝ)
    (hLip : ∀ U V : Fin K → Matrix.unitaryGroup (Fin n) ℂ,
      |F U - F V| ≤ L * Real.sqrt (∑ i, ∑ x, ∑ y,
        ‖(U i : Matrix (Fin n) (Fin n) ℂ) x y -
          (V i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2))
    (u : ℝ) (hu : 0 ≤ u) :
    SpectrumLB.haarK n K {U | u ≤ |F U - ∫ V, F V ∂SpectrumLB.haarK n K|} ≤
      ENNReal.ofReal (2 * Real.exp (-(((n : ℝ) - 2) * u ^ 2) / (24 * L ^ 2))) := by
  apply spectrum_eq_7_14_of_specialUnitary_logmean _ n K L hL F hLip u hu
  intro n K hn
  apply special_unitary_product_logmean_pushforward n K
  intro F hF L hL hLip
  exact specialUnitary_logmean_of_polynomial_logSobolev n K hn (hpoly n K hn)
    ⟨F, hF⟩ L hL hLip

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2SpectrumResolved -/
section
open MeasureTheory
open scoped Matrix ENNReal Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2

/-- Haar-unitary product concentration with the exact constants of SpectrumLB
Eq. (7.14), proved through concrete special-unitary polynomial heat. -/
theorem spectrum_eq_7_14_proved
    (n K : ℕ) (L : ℝ) (hL : 0 < L)
    (F : (Fin K → Matrix.unitaryGroup (Fin n) ℂ) → ℝ)
    (hLip : ∀ U V : Fin K → Matrix.unitaryGroup (Fin n) ℂ,
      |F U - F V| ≤ L * Real.sqrt (∑ i, ∑ x, ∑ y,
        ‖(U i : Matrix (Fin n) (Fin n) ℂ) x y -
          (V i : Matrix (Fin n) (Fin n) ℂ) x y‖ ^ 2))
    (u : ℝ) (hu : 0 ≤ u) :
    SpectrumLB.haarK n K {U | u ≤ |F U - ∫ V, F V ∂SpectrumLB.haarK n K|} ≤
      ENNReal.ofReal (2 * Real.exp (-(((n : ℝ) - 2) * u ^ 2) / (24 * L ^ 2))) := by
  exact spectrum_eq_7_14_of_polynomial_logSobolev
    specialUnitaryProduct_polynomial_logSobolev n K L hL F hLip u hu

end BosonicLearn.Prop2

end

open SpectrumLB MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder
theorem solution (d K : ℕ) (Λ : ℝ) (hΛ : 0 < Λ)
    (F : (Fin K → Matrix.unitaryGroup (Fin d) ℂ) → ℝ)
    (hF : ∀ U V : Fin K → Matrix.unitaryGroup (Fin d) ℂ,
      |F U - F V| ≤ Λ * Real.sqrt (∑ i, ∑ x, ∑ y,
        ‖(U i : Matrix (Fin d) (Fin d) ℂ) x y - (V i : Matrix (Fin d) (Fin d) ℂ) x y‖ ^ 2))
    (u : ℝ) (hu : 0 ≤ u) :
    haarK d K {U | u ≤ |F U - ∫ V, F V ∂haarK d K|} ≤
      ENNReal.ofReal (2 * Real.exp (-(((d : ℝ) - 2) * u ^ 2) / (24 * Λ ^ 2))) := BosonicLearn.Prop2.spectrum_eq_7_14_proved d K Λ hΛ F hF u hu
