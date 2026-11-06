-- Prove2me | solution 1 for QEC.Semantics.continuousOperator_commute_lindbladNoJumpPropagator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:59:35.530199+00:00
-- url     : https://prove2.me/submissions/5859af7f-587d-4d28-9e3e-601fb7bfb15b

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
    Commute (LinearMap.toContinuousLinearMap K)
      (lindbladNoJumpPropagatorContinuous K t) := by
  unfold lindbladNoJumpPropagatorContinuous
  exact ((Commute.refl (LinearMap.toContinuousLinearMap K)).smul_right
    (t : Complex)).exp_right
end QEC.Semantics
