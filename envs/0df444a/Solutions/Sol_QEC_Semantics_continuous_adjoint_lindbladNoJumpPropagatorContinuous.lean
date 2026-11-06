-- Prove2me | solution 1 for QEC.Semantics.continuous_adjoint_lindbladNoJumpPropagatorContinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:59:51.118345+00:00
-- url     : https://prove2.me/submissions/3534dd6c-771b-4c50-805e-735c3d275cbd

import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
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
theorem _root_.solution (K : Operator H) :
    Continuous (fun t : Real =>
      ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K t)) :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_adjoint_lindbladNoJumpPropagatorContinuous K t).continuousAt
end QEC.Semantics
