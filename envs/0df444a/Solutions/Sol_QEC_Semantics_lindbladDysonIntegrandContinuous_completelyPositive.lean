-- Prove2me | solution 1 for QEC.Semantics.lindbladDysonIntegrandContinuous_completelyPositive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:00:12.655723+00:00
-- url     : https://prove2.me/submissions/90cb2999-0086-48ad-b950-d40fa0ca3b15

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
theorem _root_.solution [Fintype ι]
    (K : Operator H) (J : ι → Operator H)
    (previous : Real → ContinuousSuperoperator H)
    (t s : Real)
    (hprevious : CompletelyPositive (asOperatorSuperoperator (previous s))) :
    CompletelyPositive
      (asOperatorSuperoperator
        (lindbladDysonIntegrandContinuous K J previous t s)) := by
  unfold lindbladDysonIntegrandContinuous
  rw [asOperatorSuperoperator_mul, asOperatorSuperoperator_mul,
    asOperatorSuperoperator_lindbladJumpGainContinuous]
  exact CompletelyPositive.comp hprevious
    (CompletelyPositive.comp (lindbladJumpGain_completelyPositive J)
      (lindbladNoJumpEvolutionContinuous_completelyPositive K (t - s)))
end QEC.Semantics
