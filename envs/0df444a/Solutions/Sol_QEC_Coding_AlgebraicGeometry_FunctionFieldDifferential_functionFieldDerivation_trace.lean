-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDerivation_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:15:24.571613+00:00
-- url     : https://prove2.me/submissions/4b412249-8d90-402d-b30a-d5b61fc927ad

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
private theorem derivation_trace_connection
    (D₀ : Derivation k K K) (D : Derivation k L L)
    (hD : DerivationExtends D₀ D) (T : Module.End K L) :
    D₀ (LinearMap.trace K L T) =
      LinearMap.trace K L (derivationConnection D₀ D hD T) := by
  classical
  let b := Module.finBasis K L
  let A : Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) K :=
    LinearMap.toMatrix b b T
  let B : Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) K :=
    fun i j => b.repr (D (b j)) i
  rw [LinearMap.trace_eq_matrix_trace K b, LinearMap.trace_eq_matrix_trace K b]
  simp only [Matrix.trace, map_sum]
  symm
  calc
    (∑ i, LinearMap.toMatrix b b (derivationConnection D₀ D hD T) i i) =
        ∑ i, (D₀ (A i i) + (B * A) i i - (A * B) i i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [LinearMap.toMatrix_apply, derivationConnection_repr D₀ D hD b]
      simp only [Matrix.mul_apply]
      simp only [A, B, LinearMap.toMatrix_apply]
    _ = (∑ i, D₀ (A i i)) + Matrix.trace (B * A) - Matrix.trace (A * B) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Matrix.trace,
        Matrix.diag_apply]
    _ = ∑ i, D₀ (A i i) := by
      rw [Matrix.trace_mul_comm]
      abel
    _ = ∑ i, D₀ (LinearMap.toMatrix b b T i i) := rfl
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
variable {k F : Type*} [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
theorem _root_.solution (x : F) :
    RatFuncDerivation.rationalDerivation (k := k) (M := RatFunc k) 1
        (Algebra.trace (RatFunc k) F x) =
      Algebra.trace (RatFunc k) F
        (functionFieldDerivation (k := k) (F := F) x) := by
  let D₀ := RatFuncDerivation.rationalDerivation (k := k) (M := RatFunc k) 1
  let D := functionFieldDerivation (k := k) (F := F)
  have hD : DerivationExtends D₀ D := by
    intro c
    change functionFieldDerivation (k := k) (F := F)
        (algebraMap (RatFunc k) F c) =
      algebraMap (RatFunc k) F
        (RatFuncDerivation.rationalDerivation (k := k) (M := RatFunc k) 1 c)
    rw [functionFieldDerivation,
      SeparableDerivationExtension.separableDerivationExtension_apply_algebraMap]
    let Dmap : Derivation k (RatFunc k) F :=
      (Algebra.ofId (RatFunc k) F).toLinearMap.compDer D₀
    have hmap :
        RatFuncDerivation.rationalDerivation (k := k) (M := F) 1 = Dmap := by
      have hX : Dmap RatFunc.X = (1 : F) := by
        change algebraMap (RatFunc k) F
          (RatFuncDerivation.rationalDerivation (k := k) (M := RatFunc k) 1 RatFunc.X) = 1
        rw [RatFuncDerivation.rationalDerivation_apply_X, map_one]
      rw [← hX]
      exact RatFuncDerivation.rationalDerivation_eq_of_apply_X (k := k)
    have hc := Derivation.congr_fun hmap c
    change RatFuncDerivation.rationalDerivation (k := k) (M := F) 1 c =
      algebraMap (RatFunc k) F (D₀ c) at hc
    exact hc
  rw [show Algebra.trace (RatFunc k) F x =
      LinearMap.trace (RatFunc k) F (Algebra.lmul (RatFunc k) F x) from rfl,
    show Algebra.trace (RatFunc k) F (D x) =
      LinearMap.trace (RatFunc k) F (Algebra.lmul (RatFunc k) F (D x)) from rfl,
    ← derivationConnection_lmul D₀ D hD x]
  exact derivation_trace_connection D₀ D hD (Algebra.lmul (RatFunc k) F x)
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
