-- Prove2me | solution 1 for QEC.Semantics.continuous_lindbladNoJumpEvolutionContinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:02:28.058765+00:00
-- url     : https://prove2.me/submissions/1637c206-686e-4dee-bc9e-cac6d7515dad

import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Theorems.Thm_QEC_Semantics_continuous_lindbladNoJumpPropagatorContinuous
import Theorems.Thm_QEC_Semantics_continuous_adjoint_lindbladNoJumpPropagatorContinuous

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
    Continuous (lindbladNoJumpEvolutionContinuous K) := by
  unfold lindbladNoJumpEvolutionContinuous
  exact (continuous_const.clm_apply
    (continuous_lindbladNoJumpPropagatorContinuous K)).clm_apply
      (continuous_adjoint_lindbladNoJumpPropagatorContinuous K)
end QEC.Semantics
