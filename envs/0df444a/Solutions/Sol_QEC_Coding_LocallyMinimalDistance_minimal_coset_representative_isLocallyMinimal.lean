-- Prove2me | solution 1 for QEC.Coding.LocallyMinimalDistance.minimal_coset_representative_isLocallyMinimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:53:59.820372+00:00
-- url     : https://prove2.me/submissions/c9427367-be84-4249-8b18-430de82abe5b

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.Order.Lattice.Nat
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LocallyMinimalDistance
universe u v
variable {C : Type*} [AddCommGroup C]
namespace QEC.Coding.LocallyMinimalDistance
theorem _root_.solution
    (weight : C → Nat) (B : AddSubgroup C) (moves : Finset C)
    (hmoves : ∀ m ∈ moves, m ∈ B) (c b : C) (hb : b ∈ B)
    (hmin : weight (c + b) = cosetWeight weight B c) :
    IsLocallyMinimal weight moves (c + b) := by
  intro m hm
  have hle : cosetWeight weight B c ≤ weight (c + (b + m)) := by
    apply Nat.sInf_le
    exact ⟨b + m, B.add_mem hb (hmoves m hm), rfl⟩
  rw [hmin]
  simpa only [add_assoc] using hle
end QEC.Coding.LocallyMinimalDistance
