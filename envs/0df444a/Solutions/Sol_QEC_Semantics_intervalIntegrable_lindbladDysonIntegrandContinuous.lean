-- Prove2me | solution 1 for QEC.Semantics.intervalIntegrable_lindbladDysonIntegrandContinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:06:24.479177+00:00
-- url     : https://prove2.me/submissions/808d2414-fcfe-46a0-9437-c06844f9d0e2

import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Theorems.Thm_QEC_Semantics_continuous_lindbladDysonIntegrandContinuous
import Theorems.Thm_QEC_Semantics_continuous_lindbladDysonTermContinuous

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
    (K : Operator H) (J : ι → Operator H) (n : Nat) (t : Real) :
    IntervalIntegrable
      (lindbladDysonIntegrandContinuous K J
        (lindbladDysonTermContinuous K J n) t)
      MeasureTheory.volume 0 t :=
  (continuous_lindbladDysonIntegrandContinuous K J
    (lindbladDysonTermContinuous K J n)
    (continuous_lindbladDysonTermContinuous K J n) t).intervalIntegrable 0 t
end QEC.Semantics
