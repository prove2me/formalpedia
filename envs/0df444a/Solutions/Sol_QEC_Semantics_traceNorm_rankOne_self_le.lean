-- Prove2me | solution 1 for QEC.Semantics.traceNorm_rankOne_self_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:37:08.419593+00:00
-- url     : https://prove2.me/submissions/89189ed6-6f70-40ae-aa69-eb6d44b37d8c

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
theorem _root_.solution (x : H) :
    traceNorm (InnerProductSpace.rankOne Complex x x).toLinearMap ≤ ‖x‖ ^ 2 := by
  change ‖tracePairing (InnerProductSpace.rankOne Complex x x).toLinearMap‖ ≤ ‖x‖ ^ 2
  apply (tracePairing (InnerProductSpace.rankOne Complex x x).toLinearMap).opNorm_le_bound
  · positivity
  · intro B
    rw [show tracePairing (InnerProductSpace.rankOne Complex x x).toLinearMap B =
        inner Complex x (B x) by
      change LinearMap.trace Complex H
          (B.toLinearMap * (InnerProductSpace.rankOne Complex x x).toLinearMap) = _
      rw [show B.toLinearMap * (InnerProductSpace.rankOne Complex x x).toLinearMap =
          (InnerProductSpace.rankOne Complex (B x) x).toLinearMap by
        ext y
        simp]
      exact InnerProductSpace.trace_rankOne (B x) x]
    calc
      ‖inner Complex x (B x)‖ ≤ ‖x‖ * ‖B x‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖B‖ * ‖x‖) := by
        gcongr
        exact B.le_opNorm x
      _ = ‖x‖ ^ 2 * ‖B‖ := by ring
end QEC.Semantics
