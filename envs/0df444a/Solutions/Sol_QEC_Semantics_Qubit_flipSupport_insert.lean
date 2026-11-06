-- Prove2me | solution 1 for QEC.Semantics.Qubit.flipSupport_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:41:44.684074+00:00
-- url     : https://prove2.me/submissions/58951766-1640-42c3-9357-73c42d1e79f3

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_Qubit_flipAt_apply_ne
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
omit [Fintype ι]
namespace QEC.Semantics.Qubit
theorem _root_.solution (s : Finset ι) {i : ι} (h : i ∉ s)
    (bits : Bitstring ι) :
    flipSupport (insert i s) bits = flipSupport s (flipAt i bits) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [flipSupport, h]
  · by_cases hjs : j ∈ s
    · simp [flipSupport, hji, hjs, flipAt_apply_ne bits hji]
    · simp [flipSupport, hji, hjs, flipAt_apply_ne bits hji]
end QEC.Semantics.Qubit
