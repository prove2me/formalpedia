-- Prove2me | solution 1 for QEC.Semantics.Qubit.flipSupport_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:41:49.143698+00:00
-- url     : https://prove2.me/submissions/e2cb951e-d0ed-47e9-a33c-f0912f04903b

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
omit [Fintype ι]
namespace QEC.Semantics.Qubit
theorem _root_.solution (i : ι) (bits : Bitstring ι) :
    flipSupport ({i} : Finset ι) bits = flipAt i bits := by
  funext j
  by_cases h : j = i
  · subst j
    simp [flipSupport, flipAt]
  · simp [flipSupport, flipAt, h]
end QEC.Semantics.Qubit
