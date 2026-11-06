-- Prove2me | solution 1 for QEC.Semantics.lindbladDysonTermContinuous_completelyPositive_of_intervalIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:06:04.072046+00:00
-- url     : https://prove2.me/submissions/b51d5f38-68ad-486d-afb3-856986bc4278

import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Theorems.Thm_QEC_Semantics_lindbladDysonIntegrandContinuous_completelyPositive
import Theorems.Thm_QEC_Semantics_lindbladDysonTermContinuous_zero_completelyPositive
import Theorems.Thm_QEC_Semantics_CompletelyPositive_intervalIntegral

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
    (hintegrable : ∀ n t, IntervalIntegrable
      (lindbladDysonIntegrandContinuous K J
        (lindbladDysonTermContinuous K J n) t)
      MeasureTheory.volume 0 t)
    (n : Nat) (t : Real) (ht : 0 ≤ t) :
    CompletelyPositive
      (asOperatorSuperoperator (lindbladDysonTermContinuous K J n t)) := by
  induction n generalizing t with
  | zero => exact lindbladDysonTermContinuous_zero_completelyPositive K J t
  | succ n induction =>
      change CompletelyPositive
        (asOperatorSuperoperator
          (∫ s in (0 : Real)..t,
            lindbladDysonIntegrandContinuous K J
              (lindbladDysonTermContinuous K J n) t s))
      apply CompletelyPositive.intervalIntegral _ 0 t ht (hintegrable n t)
      intro s hs
      exact lindbladDysonIntegrandContinuous_completelyPositive K J
        (lindbladDysonTermContinuous K J n) t s (induction s hs.1)
end QEC.Semantics
