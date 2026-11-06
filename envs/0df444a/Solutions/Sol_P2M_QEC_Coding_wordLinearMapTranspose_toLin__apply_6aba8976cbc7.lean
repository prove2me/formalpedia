-- Prove2me | solution 1 for P2M_QEC_Coding_wordLinearMapTranspose_toLin__apply_6aba8976cbc7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:05:03.57457+00:00
-- url     : https://prove2.me/submissions/367c405d-ac1f-42ec-8106-624d739ac888

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
    {row col : Type v} [Fintype row] [Fintype col] [DecidableEq col]
    (M : Matrix row col F) (x : Word F row) (c : col) :
    wordLinearMapTranspose (Matrix.toLin' M) x c =
      ∑ r : row, x r * M r c := by
  classical
  unfold wordLinearMapTranspose
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro r _hr
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single c]
  · simp
  · intro c' _hc' hne
    simp [hne]
  · simp
end QEC.Coding
