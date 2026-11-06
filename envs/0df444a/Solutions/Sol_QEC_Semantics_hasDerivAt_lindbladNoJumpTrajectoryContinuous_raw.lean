-- Prove2me | solution 1 for QEC.Semantics.hasDerivAt_lindbladNoJumpTrajectoryContinuous_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:59:17.637616+00:00
-- url     : https://prove2.me/submissions/fed0b86e-40e8-4146-a65a-662d798ed822

import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Theorems.Thm_QEC_Semantics_hasDerivAt_lindbladNoJumpPropagatorContinuous
import Theorems.Thm_QEC_Semantics_hasDerivAt_adjoint_lindbladNoJumpPropagatorContinuous

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
      (((lindbladNoJumpPropagatorContinuous K t *
          LinearMap.toContinuousLinearMap K) * A) *
          ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K t) +
        (lindbladNoJumpPropagatorContinuous K t * A) *
          (ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K t) *
            ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K))) t := by
  exact ((hasDerivAt_lindbladNoJumpPropagatorContinuous K t).mul_const A).mul
    (hasDerivAt_adjoint_lindbladNoJumpPropagatorContinuous K t)
end QEC.Semantics
