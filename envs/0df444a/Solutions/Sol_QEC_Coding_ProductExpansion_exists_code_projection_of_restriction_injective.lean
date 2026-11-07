-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.exists_code_projection_of_restriction_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:55:13.05729+00:00
-- url     : https://prove2.me/submissions/1262c09c-213a-4c97-a4f6-0d1b8c4b4eff

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
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
omit [DecidableEq F] [Fintype R]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (A : Finset W)
    (hInjective : Function.Injective (codeRestriction h A)) :
    ∃ T : Word F W →ₗ[F] Word F W,
      (∀ c : Word F W, c ∈ (parityCheckCode h).carrier → T c = c) ∧
      (∀ x : Word F W, (∀ i ∈ A, x i = 0) → T x = 0) ∧
      (∀ x : Word F W, T x ∈ (parityCheckCode h).carrier) := by
  let R := codeRestriction h A
  let L := R.leftInverse
  let T := (parityCheckCode h).carrier.subtype.comp
    (L.comp (restrictionLinearMap A))
  have hLeft (c : (parityCheckCode h).carrier) : L (R c) = c :=
    R.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hInjective) c
  refine ⟨T, ?_, ?_, ?_⟩
  · intro c hc
    let cc : (parityCheckCode h).carrier := ⟨c, hc⟩
    change (L (R cc) : Word F W) = c
    rw [hLeft cc]
  · intro x hx
    have hRestriction : restrictionLinearMap A x = 0 := by
      funext i
      exact hx i.1 i.2
    simp [T, hRestriction]
  · intro x
    exact (L (restrictionLinearMap A x)).2
end QEC.Coding.ProductExpansion
