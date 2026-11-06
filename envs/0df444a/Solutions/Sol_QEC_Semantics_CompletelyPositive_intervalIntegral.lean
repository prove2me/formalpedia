-- Prove2me | solution 1 for QEC.Semantics.CompletelyPositive.intervalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:03:46.283414+00:00
-- url     : https://prove2.me/submissions/3f452d05-1c43-4f67-9967-b046196b89a6

import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Theorems.Thm_QEC_Semantics_intervalIntegral_comp_comm
import Theorems.Thm_QEC_Semantics_intervalIntegral_preserves_adjoint_blocks
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg



set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
attribute [local instance] QEC.Semantics.finiteQuantumSystemComplete
open QEC.Semantics.CompletelyPositive
set_option maxHeartbeats 800000
namespace QEC.Semantics.CompletelyPositive
theorem _root_.solution
    (f : Real → ContinuousSuperoperator H) (a b : Real) (hab : a ≤ b)
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hcp : ∀ s ∈ Set.Icc a b,
      CompletelyPositive (asOperatorSuperoperator (f s))) :
    CompletelyPositive (asOperatorSuperoperator (∫ s in a..b, f s)) := by
  intro n M hM
  constructor
  · intro i j
    exact intervalIntegral_preserves_adjoint_blocks f a b hf hab (M i j) (M j i)
      (fun s hs => (hcp s hs n M hM).1 i j)
  · intro x
    let q := completelyPositiveQuadraticFunctional n M x
    have hnonneg : 0 ≤ ∫ s in a..b, q (f s) :=
      intervalIntegral.integral_nonneg hab fun s hs => by
        simpa [q, completelyPositiveQuadraticFunctional_apply, OperatorMatrix.map] using
          (hcp s hs n M hM).2 x
    rw [intervalIntegral_comp_comm q f a b hf] at hnonneg
    simpa [q, completelyPositiveQuadraticFunctional_apply, OperatorMatrix.map] using hnonneg
end QEC.Semantics.CompletelyPositive
