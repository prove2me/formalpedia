-- Prove2me | solution 1 for QEC.Semantics.finiteLindbladEvolutionLinearMap_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:03:29.100926+00:00
-- url     : https://prove2.me/submissions/b23500a0-60a6-4701-b8b7-5ed2eb1f9ba5

import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionLinearMap_zero
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


attribute [local simp] QEC.Semantics.finiteLindbladEvolutionLinearMap_zero

set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
attribute [local instance] QEC.Semantics.finiteQuantumSystemComplete
namespace QEC.Semantics
theorem _root_.solution [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) (t s : Real) :
    finiteLindbladEvolutionLinearMap hamiltonian J (t + s) =
      (finiteLindbladEvolutionLinearMap hamiltonian J t).comp
        (finiteLindbladEvolutionLinearMap hamiltonian J s) := by
  let G := asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)
  have hsmul : ((t + s : Real) : Complex) • G =
      (t : Complex) • G + (s : Complex) • G := by
    calc
      ((t + s : Real) : Complex) • G =
          ((t : Complex) + (s : Complex)) • G := by rw [Complex.ofReal_add]
      _ = (t : Complex) • G + (s : Complex) • G := by
        ext A x
        simp
        module
  have hcomm : Commute ((t : Complex) • G) ((s : Complex) • G) := by
    rw [Commute]
    ext A x
    simp
    module
  let _ : NormedAlgebra ℚ (ContinuousSuperoperator H) :=
    NormedAlgebra.restrictScalars ℚ Complex (ContinuousSuperoperator H)
  unfold finiteLindbladEvolutionLinearMap finiteLindbladEvolutionContinuous
  change asOperatorSuperoperator (NormedSpace.exp (((t + s : Real) : Complex) • G)) =
    (asOperatorSuperoperator (NormedSpace.exp ((t : Complex) • G))).comp
      (asOperatorSuperoperator (NormedSpace.exp ((s : Complex) • G)))
  rw [hsmul, NormedSpace.exp_add_of_commute hcomm,
    asOperatorSuperoperator_mul]
end QEC.Semantics
