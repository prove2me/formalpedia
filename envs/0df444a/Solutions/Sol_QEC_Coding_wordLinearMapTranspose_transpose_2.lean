-- Prove2me | solution 2 for QEC.Coding.wordLinearMapTranspose_transpose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:37:37.65078+00:00
-- url     : https://prove2.me/submissions/2fd38a9a-eb5f-4537-b9c5-cfb3c23de595

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding
universe u v
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {i0 i1 i2 : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]
namespace QEC.Coding
theorem _root_.solution
    (f : Word F i0 →ₗ[F] Word F i1) :
    wordLinearMapTranspose (wordLinearMapTranspose f) = f := by
  apply LinearMap.ext
  intro x
  rw [← sub_eq_zero]
  apply (wordPairing_nondegenerate (F := F)).right
  intro y
  have hPair :
      wordPairing (F := F) y
          (wordLinearMapTranspose (wordLinearMapTranspose f) x) =
        wordPairing (F := F) y (f x) := by
    calc
      wordPairing (F := F) y
          (wordLinearMapTranspose (wordLinearMapTranspose f) x) =
          wordPairing (F := F)
            (wordLinearMapTranspose (wordLinearMapTranspose f) x) y := by
        simp [wordPairing_apply, dotProduct_comm]
      _ = wordPairing (F := F) x
            (wordLinearMapTranspose f y) :=
        wordPairing_wordLinearMapTranspose
          (wordLinearMapTranspose f) x y
      _ = wordPairing (F := F)
            (wordLinearMapTranspose f y) x := by
        simp [wordPairing_apply, dotProduct_comm]
      _ = wordPairing (F := F) y (f x) :=
        wordPairing_wordLinearMapTranspose f y x
  simpa [wordPairing_apply, dotProduct_sub] using
    sub_eq_zero.mpr hPair
end QEC.Coding
