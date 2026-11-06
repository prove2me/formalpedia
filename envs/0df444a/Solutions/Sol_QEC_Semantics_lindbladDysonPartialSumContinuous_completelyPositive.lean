-- Prove2me | solution 1 for QEC.Semantics.lindbladDysonPartialSumContinuous_completelyPositive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:03:18.7848+00:00
-- url     : https://prove2.me/submissions/5e34a565-4ae3-4b1d-98f5-9da60ac1223c

import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Theorems.Thm_QEC_Semantics_CompletelyPositive_sum_finset
import Theorems.Thm_QEC_Semantics_asOperatorSuperoperator_finset_sum
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
theorem _root_.solution [Fintype ι]
    (K : Operator H) (J : ι → Operator H)
    (N : Nat) (t : Real) (ht : 0 ≤ t) :
    CompletelyPositive
      (asOperatorSuperoperator (lindbladDysonPartialSumContinuous K J N t)) := by
  rw [lindbladDysonPartialSumContinuous,
    asOperatorSuperoperator_finset_sum]
  exact CompletelyPositive.sum_finset (Finset.range (N + 1))
    (fun n _hn => lindbladDysonTermContinuous_completelyPositive K J n t ht)
end QEC.Semantics
