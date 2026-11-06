-- Prove2me | solution 1 for QEC.Semantics.Qubit.localZMatrix_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:41:35.356255+00:00
-- url     : https://prove2.me/submissions/dfe4df18-2315-44c5-a6b4-51aa227c65a1

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
omit [DecidableEq ι]
namespace QEC.Semantics.Qubit
theorem _root_.solution (i : ι) :
    (localZMatrix i).conjTranspose = localZMatrix i := by
  classical
  ext row col
  change star (localZMatrix i col row) = localZMatrix i row col
  by_cases h : row = col
  · subst col
    simp [localZMatrix]
  · have hc : ¬ col = row := fun hc => h hc.symm
    simp [localZMatrix, h, hc]
end QEC.Semantics.Qubit
