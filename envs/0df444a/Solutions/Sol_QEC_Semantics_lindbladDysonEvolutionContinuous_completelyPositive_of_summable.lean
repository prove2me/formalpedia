-- Prove2me | solution 1 for QEC.Semantics.lindbladDysonEvolutionContinuous_completelyPositive_of_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:03:19.67147+00:00
-- url     : https://prove2.me/submissions/1663e24a-9a0c-4c25-9ea7-91d0d5c39662

import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Theorems.Thm_QEC_Semantics_lindbladDysonTermContinuous_completelyPositive

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
    [Fintype ι] (K : Operator H) (J : ι → Operator H)
    (t : Real) (ht : 0 ≤ t)
    (hsummable : Summable (fun n => lindbladDysonTermContinuous K J n t)) :
    CompletelyPositive
      (asOperatorSuperoperator (lindbladDysonEvolutionContinuous K J t)) := by
  unfold lindbladDysonEvolutionContinuous
  exact CompletelyPositive.tsum _ hsummable
    (fun n => lindbladDysonTermContinuous_completelyPositive K J n t ht)
end QEC.Semantics
