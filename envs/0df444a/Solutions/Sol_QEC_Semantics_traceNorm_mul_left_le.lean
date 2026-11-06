-- Prove2me | solution 1 for QEC.Semantics.traceNorm_mul_left_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:09:30.070965+00:00
-- url     : https://prove2.me/submissions/9627f34f-9349-4321-993b-8c44c0506cc5

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
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
theorem _root_.solution (A B : Operator H) :
    traceNorm (A * B) ≤ operatorNorm A * traceNorm B := by
  change ‖tracePairing (A * B)‖ ≤ ‖LinearMap.toContinuousLinearMap A‖ * ‖tracePairing B‖
  apply (tracePairing (A * B)).opNorm_le_bound
  · exact mul_nonneg (ContinuousLinearMap.opNorm_nonneg _)
      (ContinuousLinearMap.opNorm_nonneg _)
  · intro C
    rw [show tracePairing (A * B) C =
        tracePairing B (C * LinearMap.toContinuousLinearMap A) by
      simp [tracePairing, mul_assoc]]
    calc
      ‖tracePairing B (C * LinearMap.toContinuousLinearMap A)‖ ≤
          traceNorm B * ‖C * LinearMap.toContinuousLinearMap A‖ :=
        (tracePairing B).le_opNorm _
      _ ≤ traceNorm B * (‖C‖ * operatorNorm A) := by
        exact mul_le_mul_of_nonneg_left
          (C.opNorm_comp_le (LinearMap.toContinuousLinearMap A))
          (ContinuousLinearMap.opNorm_nonneg _)
      _ = (operatorNorm A * traceNorm B) * ‖C‖ := by ring
end QEC.Semantics
