-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.derivation_logarithmic_trace_eq_matrix_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:48:55.599378+00:00
-- url     : https://prove2.me/submissions/8df6cea4-1a38-48fe-b189-dad81587900b

import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DerivationTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one


section
namespace QEC.Coding.AlgebraicGeometry
namespace FunctionFieldDifferential
open scoped RatFunc
section ConnectionTrace
variable {k K L : Type*} [Field k] [Field K] [Field L]
variable [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
variable [FiniteDimensional K L]
private theorem derivation_repr
    (D₀ : Derivation k K K) (D : Derivation k L L)
    (hD : DerivationExtends D₀ D) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K L) (x : L) (i : ι) :
    b.repr (D x) i =
      D₀ (b.repr x i) +
        ∑ j : ι, b.repr x j * b.repr (D (b j)) i := by
  classical
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum]
  simp_rw [derivation_smul_of_extends D₀ D hD]
  simp only [map_sum, map_add, map_smul, b.repr_self]
  rw [Finset.sum_add_distrib]
  simp [Finsupp.single_apply]
private theorem derivationConnection_repr
    (D₀ : Derivation k K K) (D : Derivation k L L)
    (hD : DerivationExtends D₀ D) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K L) (T : Module.End K L) (i j : ι) :
    b.repr (derivationConnection D₀ D hD T (b j)) i =
      D₀ (b.repr (T (b j)) i) +
        ∑ r : ι, b.repr (D (b r)) i * b.repr (T (b j)) r -
          ∑ r : ι, b.repr (T (b r)) i * b.repr (D (b j)) r := by
  rw [derivationConnection]
  change b.repr (D (T (b j)) - T (D (b j))) i = _
  rw [map_sub, Finsupp.sub_apply, derivation_repr D₀ D hD b]
  have hTD :
      b.repr (T (D (b j))) i =
        ∑ r : ι, b.repr (T (b r)) i * b.repr (D (b j)) r := by
    change ((b.coord i).comp T) (D (b j)) = _
    conv_lhs => rw [← b.sum_repr (D (b j))]
    rw [map_sum]
    simp only [map_smul, LinearMap.comp_apply, b.coord_apply]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hTD]
  congr 2
  · apply Finset.sum_congr rfl
    intro r _
    ring
private theorem derivationConnection_lmul
    (D₀ : Derivation k K K) (D : Derivation k L L)
    (hD : DerivationExtends D₀ D) (x : L) :
    derivationConnection D₀ D hD (Algebra.lmul K L x) =
      Algebra.lmul K L (D x) := by
  ext y
  change D (x * y) - x * D y = D x * y
  rw [D.leibniz]
  ring
end ConnectionTrace
variable {k F : Type*} [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
end FunctionFieldDifferential
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped RatFunc
variable {k K L : Type*} [Field k] [Field K] [Field L]
variable [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
variable [FiniteDimensional K L]
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
theorem _root_.solution
    (D₀ : Derivation k K K) (D : Derivation k L L)
    (hD : ∀ c : K, D (algebraMap K L c) = algebraMap K L (D₀ c))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L)
    (r t : L) (ht : t ≠ 0) :
    Algebra.trace K L (r * D t * t⁻¹) =
      Matrix.trace
        (LinearMap.toMatrix b b (Algebra.lmul K L r) *
          LinearMap.toMatrix b b (Algebra.lmul K L t⁻¹) *
            entrywiseMatrixDerivation D₀
              (LinearMap.toMatrix b b (Algebra.lmul K L t))) := by
  classical
  let A := LinearMap.toMatrix b b (Algebra.lmul K L t)
  let U := LinearMap.toMatrix b b (Algebra.lmul K L t⁻¹)
  let R := LinearMap.toMatrix b b (Algebra.lmul K L r)
  let B : Matrix ι ι K := fun i j => b.repr (D (b j)) i
  let E : Matrix ι ι K := entrywiseMatrixDerivation D₀ A
  have hconnection :
      LinearMap.toMatrix b b (Algebra.lmul K L (D t)) =
        E + B * A - A * B := by
    rw [← derivationConnection_lmul D₀ D hD t]
    ext i j
    rw [LinearMap.toMatrix_apply,
      derivationConnection_repr D₀ D hD b]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply]
    simp only [E, B, A, LinearMap.toMatrix_apply,
      entrywiseMatrixDerivation_apply]
  have hAU : A * U = 1 := by
    dsimp only [A, U]
    rw [← LinearMap.toMatrix_mul, ← map_mul, mul_inv_cancel₀ ht,
      map_one, LinearMap.toMatrix_one]
  have hUA : U * A = 1 := by
    dsimp only [A, U]
    rw [← LinearMap.toMatrix_mul, ← map_mul, inv_mul_cancel₀ ht,
      map_one, LinearMap.toMatrix_one]
  have hUR : U * R = R * U := by
    calc
      U * R = LinearMap.toMatrix b b (Algebra.lmul K L (t⁻¹ * r)) := by
        rw [map_mul, LinearMap.toMatrix_mul]
      _ = LinearMap.toMatrix b b (Algebra.lmul K L (r * t⁻¹)) := by
        rw [mul_comm]
      _ = R * U := by
        rw [map_mul, LinearMap.toMatrix_mul]
  have hURA : U * (R * A) = R := by
    calc
      U * (R * A) = (U * R) * A := by rw [Matrix.mul_assoc]
      _ = (R * U) * A := by rw [hUR]
      _ = R * (U * A) := by rw [Matrix.mul_assoc]
      _ = R := by rw [hUA, mul_one]
  have htrace_E : Matrix.trace (R * E * U) = Matrix.trace (R * U * E) := by
    calc
      Matrix.trace (R * E * U) = Matrix.trace (U * R * E) :=
        Matrix.trace_mul_cycle R E U
      _ = Matrix.trace (R * U * E) := by rw [hUR]
  have htrace_BA : Matrix.trace (R * B * A * U) = Matrix.trace (R * B) := by
    rw [Matrix.mul_assoc (R * B) A U, hAU, mul_one]
  have htrace_AB : Matrix.trace (R * A * B * U) = Matrix.trace (R * B) := by
    calc
      Matrix.trace (R * A * B * U) = Matrix.trace (U * (R * A * B)) :=
        Matrix.trace_mul_comm (R * A * B) U
      _ = Matrix.trace ((U * (R * A)) * B) := by
        rw [Matrix.mul_assoc U (R * A) B]
      _ = Matrix.trace (R * B) := by rw [hURA]
  have hlmul : Algebra.lmul K L (r * D t * t⁻¹) =
      Algebra.lmul K L r * Algebra.lmul K L (D t) * Algebra.lmul K L t⁻¹ := by
    ext x
    change (r * D t * t⁻¹) * x = r * (D t * (t⁻¹ * x))
    ring
  rw [show Algebra.trace K L (r * D t * t⁻¹) =
      LinearMap.trace K L (Algebra.lmul K L (r * D t * t⁻¹)) from rfl,
    LinearMap.trace_eq_matrix_trace K b]
  change Matrix.trace
      (LinearMap.toMatrix b b (Algebra.lmul K L (r * D t * t⁻¹))) = _
  calc
    _ = Matrix.trace (R * (E + B * A - A * B) * U) := by
      congr 1
      rw [hlmul, LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, hconnection]
    _ = Matrix.trace (R * E * U) + Matrix.trace (R * B * A * U) -
        Matrix.trace (R * A * B * U) := by
      simp only [mul_sub, mul_add, sub_mul, add_mul, Matrix.trace_sub,
        Matrix.trace_add, Matrix.mul_assoc]
    _ = Matrix.trace (R * E * U) := by rw [htrace_BA, htrace_AB, add_sub_cancel_right]
    _ = Matrix.trace (R * U * E) := htrace_E
    _ = _ := by rfl
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
