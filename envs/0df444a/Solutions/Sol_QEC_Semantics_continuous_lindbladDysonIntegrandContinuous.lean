-- Prove2me | solution 1 for QEC.Semantics.continuous_lindbladDysonIntegrandContinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:04:33.55636+00:00
-- url     : https://prove2.me/submissions/9c0143f2-09cd-4caf-a9ba-ab4bb169023c

import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Theorems.Thm_QEC_Semantics_continuous_lindbladNoJumpEvolutionContinuous

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
    (hprevious : Continuous previous) (t : Real) :
    Continuous (lindbladDysonIntegrandContinuous K J previous t) := by
  unfold lindbladDysonIntegrandContinuous
  exact (((continuous_lindbladNoJumpEvolutionContinuous K).comp
    (continuous_const.sub continuous_id)).mul continuous_const).mul hprevious
end QEC.Semantics
