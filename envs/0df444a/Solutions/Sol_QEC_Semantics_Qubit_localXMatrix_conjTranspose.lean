-- Prove2me | solution 1 for QEC.Semantics.Qubit.localXMatrix_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:41:20.965335+00:00
-- url     : https://prove2.me/submissions/8ef20b2a-4dc6-404e-bf2e-adf645f3b549

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators ComplexOrder
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.Qubit
theorem _root_.solution (i : ι) :
    (localXMatrix i).conjTranspose = localXMatrix i := by
  classical
  ext row col
  change star (localXMatrix i col row) = localXMatrix i row col
  by_cases h : row = flipAt i col
  · have hc : col = flipAt i row := by
      rw [h, flipAt_flipAt]
    have hleft : localXMatrix i col row = 1 := by
      unfold localXMatrix
      exact if_pos hc
    have hright : localXMatrix i row col = 1 := by
      unfold localXMatrix
      exact if_pos h
    rw [hleft, hright]
    simp
  · have hc : ¬ col = flipAt i row := by
      intro hc
      apply h
      rw [hc, flipAt_flipAt]
    have hleft : localXMatrix i col row = 0 := by
      unfold localXMatrix
      exact if_neg hc
    have hright : localXMatrix i row col = 0 := by
      unfold localXMatrix
      exact if_neg h
    rw [hleft, hright]
    simp
end QEC.Semantics.Qubit
