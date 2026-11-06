-- Prove2me | solution 1 for QEC.Semantics.lindbladDysonTermContinuous_completelyPositive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:09:18.86581+00:00
-- url     : https://prove2.me/submissions/af09c46d-4412-47cd-8f18-68f96b64acd7

import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Theorems.Thm_QEC_Semantics_intervalIntegrable_lindbladDysonIntegrandContinuous
import Theorems.Thm_QEC_Semantics_lindbladDysonTermContinuous_completelyPositive_of_intervalIntegrable

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
    (n : Nat) (t : Real) (ht : 0 ≤ t) :
    CompletelyPositive
      (asOperatorSuperoperator (lindbladDysonTermContinuous K J n t)) :=
  lindbladDysonTermContinuous_completelyPositive_of_intervalIntegrable K J
    (intervalIntegrable_lindbladDysonIntegrandContinuous K J) n t ht
end QEC.Semantics
