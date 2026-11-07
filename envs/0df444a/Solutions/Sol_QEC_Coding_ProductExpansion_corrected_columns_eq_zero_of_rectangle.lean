-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.corrected_columns_eq_zero_of_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:56:51.911266+00:00
-- url     : https://prove2.me/submissions/7e0c7149-d59c-4c9a-8426-71d8a19058ce

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_codeword_eq_zero_of_vanish_on_large_subset
import Theorems.Thm_QEC_Coding_ProductExpansion_column_mem_parityCheckCode_of_left_mul_eq_zero
import Theorems.Thm_QEC_Coding_ProductExpansion_mapRows_eq_zero_on_rows_of_vanish_on_rectangle
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (d : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (A B : Finset W) (hLarge : Fintype.card W - d < B.card)
    (T : Word F W →ₗ[F] Word F W)
    (hVanish : ∀ y : Word F W, (∀ j ∈ A, y j = 0) → T y = 0)
    (x : Matrix W W F) (hx : ∀ i ∈ B, ∀ j ∈ A, x i j = 0)
    (hLeft : h * (x - mapRows T x) = 0) :
    ∀ j ∈ A, column (x - mapRows T x) j = 0 := by
  intro j hj
  apply codeword_eq_zero_of_vanish_on_large_subset h d hDistance B hLarge
  · exact column_mem_parityCheckCode_of_left_mul_eq_zero
      h (x - mapRows T x) hLeft j
  · intro i hi
    have hProjected : mapRows T x i = 0 :=
      mapRows_eq_zero_on_rows_of_vanish_on_rectangle T A B hVanish x hx i hi
    simp [column, hx i hi j hj, hProjected]
end QEC.Coding.ProductExpansion
