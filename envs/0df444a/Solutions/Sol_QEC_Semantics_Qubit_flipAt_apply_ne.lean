-- Prove2me | solution 1 for QEC.Semantics.Qubit.flipAt_apply_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:22:30.404514+00:00
-- url     : https://prove2.me/submissions/486bc24c-75a1-4cfb-9cee-a9f0d20f0639

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
namespace QEC.Semantics.Qubit
theorem _root_.solution {ι : Type u} [DecidableEq ι]
    {i j : ι} (bits : Bitstring ι) (h : j ≠ i) :
    flipAt i bits j = bits j := by
  simp [flipAt, h]
end QEC.Semantics.Qubit
