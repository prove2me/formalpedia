-- Prove2me | solution 1 for QEC.Semantics.continuous_lindbladDysonTermContinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:04:50.192977+00:00
-- url     : https://prove2.me/submissions/8b04e1da-100b-477e-9759-a3165eb9b66a

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
    (K : Operator H) (J : ι → Operator H) (n : Nat) :
    Continuous (lindbladDysonTermContinuous K J n) := by
  induction n with
  | zero => exact continuous_lindbladNoJumpEvolutionContinuous K
  | succ n induction =>
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      · change Continuous (fun p : Real × Real =>
          lindbladDysonIntegrandContinuous K J
            (lindbladDysonTermContinuous K J n) p.1 p.2)
        unfold lindbladDysonIntegrandContinuous
        exact (((continuous_lindbladNoJumpEvolutionContinuous K).comp
          (continuous_fst.sub continuous_snd)).mul continuous_const).mul
            (induction.comp continuous_snd)
      · exact continuous_id
end QEC.Semantics
