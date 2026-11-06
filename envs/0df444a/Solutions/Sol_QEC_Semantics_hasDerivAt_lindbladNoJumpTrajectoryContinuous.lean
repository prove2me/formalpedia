-- Prove2me | solution 1 for QEC.Semantics.hasDerivAt_lindbladNoJumpTrajectoryContinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:03:17.973827+00:00
-- url     : https://prove2.me/submissions/0395cabf-107c-4caa-9562-8aa9dcabfef4

import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Theorems.Thm_QEC_Semantics_hasDerivAt_lindbladNoJumpTrajectoryContinuous_raw
import Theorems.Thm_QEC_Semantics_continuousOperator_commute_lindbladNoJumpPropagator
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
namespace QEC.Semantics
theorem _root_.solution
    (K : Operator H) (A : ContinuousOperator H) (t : Real) :
    HasDerivAt (lindbladNoJumpTrajectoryContinuous K A)
      (LinearMap.toContinuousLinearMap K *
          lindbladNoJumpTrajectoryContinuous K A t +
        lindbladNoJumpTrajectoryContinuous K A t *
          ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K)) t := by
  convert hasDerivAt_lindbladNoJumpTrajectoryContinuous_raw K A t using 1
  rw [(continuousOperator_commute_lindbladNoJumpPropagator K t).eq.symm]
  simp only [lindbladNoJumpTrajectoryContinuous, mul_assoc]
end QEC.Semantics
