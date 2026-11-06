-- Prove2me | solution 1 for QEC.Semantics.CompletelyPositive.sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:03:08.755846+00:00
-- url     : https://prove2.me/submissions/8a6d641a-a78e-4a85-9406-1300295d4337

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

set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
attribute [local instance] QEC.Semantics.finiteQuantumSystemComplete
open QEC.Semantics.CompletelyPositive
variable {K L : Type u}
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
namespace QEC.Semantics.CompletelyPositive
theorem _root_.solution {κ : Type*} [Fintype κ]
    {Φ : κ → Operator H →ₗ[Complex] Operator K}
    (hΦ : ∀ i, CompletelyPositive (Φ i)) :
    CompletelyPositive (∑ i, Φ i) := by
  classical
  exact sum_finset Finset.univ fun i _hi => hΦ i
end QEC.Semantics.CompletelyPositive
