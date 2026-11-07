-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.HammingWeight_le_complement_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:35:05.983215+00:00
-- url     : https://prove2.me/submissions/5f927771-047d-43e5-b000-9a024308fbe7

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
omit [Fintype F] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (A : Finset W) (x : Word F W) (hVanish : ∀ j ∈ A, x j = 0) :
    HammingWeight x ≤ Fintype.card W - A.card := by
  classical
  have hSupport : hammingSupport x ⊆ Finset.univ \ A := by
    intro j hj
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hjA
    have hxj : x j ≠ 0 := by simpa [hammingSupport] using hj
    exact hxj (hVanish j hjA)
  have hCard := Finset.card_le_card hSupport
  have hComplement : (Finset.univ \ A).card = Fintype.card W - A.card := by
    simpa using Finset.card_sdiff_of_subset (Finset.subset_univ A)
  simpa [HammingWeight, hComplement] using hCard
end QEC.Coding.ProductExpansion
