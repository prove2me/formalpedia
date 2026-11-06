-- Prove2me | solution 1 for QEC.Semantics.hasDerivAt_adjoint_lindbladNoJumpPropagatorContinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:23:41.761142+00:00
-- url     : https://prove2.me/submissions/6dca6d86-7496-4ec8-9c7f-7087eb7ac236

import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_QEC_Semantics_Dynamics_Lindblad

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
    (K : Operator H) (t : Real) :
    HasDerivAt
      (fun s : Real =>
        ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K s))
      (ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K t) *
        ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K)) t := by
  rw [show (fun s : Real =>
      ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K s)) =
      (fun s : Real => NormedSpace.exp ((s : Complex) •
        ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K))) by
    funext s
    exact adjoint_lindbladNoJumpPropagatorContinuous K s]
  let _ : NormedAlgebra Real (ContinuousOperator H) :=
    NormedAlgebra.restrictScalars Real Complex (ContinuousOperator H)
  rw [adjoint_lindbladNoJumpPropagatorContinuous]
  change HasDerivAt
    (fun s : Real => NormedSpace.exp
      (s • ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K)))
    (NormedSpace.exp (t • ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K)) *
      ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K)) t
  exact hasDerivAt_exp_smul_const
    (ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K)) t
end QEC.Semantics
