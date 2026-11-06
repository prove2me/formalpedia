-- Prove2me | solution 1 for QEC.Semantics.traceNorm_mul_right_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:18:49.021657+00:00
-- url     : https://prove2.me/submissions/d2401ddf-8655-4a57-8957-719ef45c0523

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm

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
    traceNorm (A * B) ≤ operatorNorm B * traceNorm A := by
  change ‖tracePairing (A * B)‖ ≤ ‖LinearMap.toContinuousLinearMap B‖ * ‖tracePairing A‖
  apply (tracePairing (A * B)).opNorm_le_bound
  · exact mul_nonneg (ContinuousLinearMap.opNorm_nonneg _)
      (ContinuousLinearMap.opNorm_nonneg _)
  · intro C
    rw [show tracePairing (A * B) C =
        tracePairing A (LinearMap.toContinuousLinearMap B * C) by
      change LinearMap.trace Complex H (C.toLinearMap * (A * B)) =
        LinearMap.trace Complex H
          ((LinearMap.toContinuousLinearMap B * C).toLinearMap * A)
      rw [show (LinearMap.toContinuousLinearMap B * C).toLinearMap =
          B * C.toLinearMap by
        ext x
        rfl]
      rw [← mul_assoc, LinearMap.trace_mul_cycle]]
    calc
      ‖tracePairing A (LinearMap.toContinuousLinearMap B * C)‖ ≤
          traceNorm A * ‖LinearMap.toContinuousLinearMap B * C‖ :=
        (tracePairing A).le_opNorm _
      _ ≤ traceNorm A * (operatorNorm B * ‖C‖) := by
        exact mul_le_mul_of_nonneg_left
          ((LinearMap.toContinuousLinearMap B).opNorm_comp_le C)
          (ContinuousLinearMap.opNorm_nonneg _)
      _ = (operatorNorm B * traceNorm A) * ‖C‖ := by ring
end QEC.Semantics
