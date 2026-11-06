-- Prove2me | solution 1 for QEC.Semantics.traceNorm_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:41:24.574295+00:00
-- url     : https://prove2.me/submissions/2c2f1f02-d8ab-4897-a985-83ea41a3ff24

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Theorems.Thm_QEC_Semantics_trace_adjoint_mul_self_eq_zero_iff
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics
theorem _root_.solution (A : Operator H) : traceNorm A = 0 ↔ A = 0 := by
  rw [traceNorm, ContinuousLinearMap.opNorm_zero_iff]
  constructor
  · intro h
    have hpair := congrArg
      (fun f : (H →L[Complex] H) →L[Complex] Complex =>
        f (LinearMap.toContinuousLinearMap (LinearMap.adjoint A))) h
    simp only [tracePairing] at hpair
    exact (trace_adjoint_mul_self_eq_zero_iff A).mp hpair
  · rintro rfl
    ext B
    simp [tracePairing]
end QEC.Semantics
