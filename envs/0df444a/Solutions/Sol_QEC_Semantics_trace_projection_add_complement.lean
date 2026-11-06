-- Prove2me | solution 1 for QEC.Semantics.trace_projection_add_complement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:52:43.734694+00:00
-- url     : https://prove2.me/submissions/634b0718-dd46-470a-9f3f-370ea6b6cbd5

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Theorems.Thm_QEC_Semantics_traceNorm_neg
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Semantics.traceNorm_neg

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics
theorem _root_.solution (P A : Operator H) :
    LinearMap.trace Complex H (P * A) +
      LinearMap.trace Complex H ((1 - P) * A) =
        LinearMap.trace Complex H A := by
  rw [← map_add, ← add_mul]
  simp
end QEC.Semantics
