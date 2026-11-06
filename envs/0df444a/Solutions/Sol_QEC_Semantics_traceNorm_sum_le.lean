-- Prove2me | solution 1 for QEC.Semantics.traceNorm_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:36:49.643231+00:00
-- url     : https://prove2.me/submissions/8ccd6d67-09a0-447f-8514-79427cd67ce3

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
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → Operator H) :
    traceNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, traceNorm (f i) := by
  classical
  change
    ‖tracePairing (∑ i ∈ s, f i)‖ ≤
      ∑ i ∈ s, ‖tracePairing (f i)‖
  rw [show
    tracePairing (∑ i ∈ s, f i) =
      ∑ i ∈ s, tracePairing (f i) by
    ext C
    simp [tracePairing, Finset.mul_sum]]
  exact norm_sum_le s (fun i => tracePairing (f i))
end QEC.Semantics
