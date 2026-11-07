-- Prove2me | solution 1 for QEC.Coding.LocallyMinimalDistance.exists_nonzero_locallyMinimal_cycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:55:39.437512+00:00
-- url     : https://prove2.me/submissions/ce1c0796-b535-4a07-89a3-dc22b5177281

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.Order.Lattice.Nat
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Theorems.Thm_QEC_Coding_LocallyMinimalDistance_exists_minimal_coset_representative
import Theorems.Thm_QEC_Coding_LocallyMinimalDistance_minimal_coset_representative_isLocallyMinimal
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
    (weight : C → Nat) (Z B : AddSubgroup C) (moves : Finset C)
    (hBZ : B ≤ Z) (hmoves : ∀ m ∈ moves, m ∈ B)
    (c : C) (hcZ : c ∈ Z) (hcB : c ∉ B) :
    ∃ c' : C, c' ∈ Z ∧ c' ≠ 0 ∧ IsLocallyMinimal weight moves c' ∧
      weight c' ≤ weight c := by
  obtain ⟨b, hb, hmin⟩ := exists_minimal_coset_representative weight B c
  refine ⟨c + b, Z.add_mem hcZ (hBZ hb), ?_,
    minimal_coset_representative_isLocallyMinimal weight B moves hmoves c b hb hmin,
    ?_⟩
  · intro hzero
    apply hcB
    have hc : c = -b := by
      exact eq_neg_of_add_eq_zero_left hzero
    rw [hc]
    exact B.neg_mem hb
  · rw [hmin]
    apply Nat.sInf_le
    exact ⟨0, B.zero_mem, by simp⟩
end QEC.Coding.LocallyMinimalDistance
