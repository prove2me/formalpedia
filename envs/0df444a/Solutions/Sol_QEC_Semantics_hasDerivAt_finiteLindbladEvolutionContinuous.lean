-- Prove2me | solution 1 for QEC.Semantics.hasDerivAt_finiteLindbladEvolutionContinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:02:47.846075+00:00
-- url     : https://prove2.me/submissions/bd1a5223-b4c4-4255-aefc-a5faa245958e

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
    (hamiltonian : Operator H) (J : ι → Operator H) (z : Complex) :
    HasDerivAt (finiteLindbladEvolutionContinuous hamiltonian J)
      (finiteLindbladEvolutionContinuous hamiltonian J z *
        asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) z := by
  exact hasDerivAt_exp_smul_const
    (asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) z
end QEC.Semantics
