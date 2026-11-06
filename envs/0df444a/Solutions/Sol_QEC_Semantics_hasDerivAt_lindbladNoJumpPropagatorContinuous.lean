-- Prove2me | solution 1 for QEC.Semantics.hasDerivAt_lindbladNoJumpPropagatorContinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:23:37.318478+00:00
-- url     : https://prove2.me/submissions/1932ce66-3312-4aeb-9f3e-64b4551b57aa

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
    HasDerivAt (lindbladNoJumpPropagatorContinuous K)
      (lindbladNoJumpPropagatorContinuous K t *
        LinearMap.toContinuousLinearMap K) t := by
  let _ : NormedAlgebra Real (ContinuousOperator H) :=
    NormedAlgebra.restrictScalars Real Complex (ContinuousOperator H)
  change HasDerivAt
    (fun s : Real => NormedSpace.exp (s • LinearMap.toContinuousLinearMap K))
    (NormedSpace.exp (t • LinearMap.toContinuousLinearMap K) *
      LinearMap.toContinuousLinearMap K) t
  exact hasDerivAt_exp_smul_const (LinearMap.toContinuousLinearMap K) t
end QEC.Semantics
