-- Prove2me | solution 1 for QEC.Semantics.norm_trace_le_traceNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:19:19.813207+00:00
-- url     : https://prove2.me/submissions/10131e69-1968-413d-a767-392cb673c972

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
theorem _root_.solution [Nontrivial H] (A : Operator H) :
    ‖LinearMap.trace Complex H A‖ ≤ traceNorm A := by
  have h := (tracePairing A).le_opNorm (ContinuousLinearMap.id Complex H)
  simpa [tracePairing, traceNorm, show (LinearMap.id : Operator H) = 1 from rfl] using h
end QEC.Semantics
