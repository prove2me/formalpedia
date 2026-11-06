-- Prove2me | solution 1 for QEC.Semantics.hasDerivAt_finiteLindbladEvolutionReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:24:44.005391+00:00
-- url     : https://prove2.me/submissions/b0e91e32-606d-468b-b7b3-5fe31f51bb62

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
    (hamiltonian : Operator H) (J : ι → Operator H) (t : Real) :
    HasDerivAt
      (fun s : Real => finiteLindbladEvolutionContinuous hamiltonian J (s : Complex))
      (finiteLindbladEvolutionContinuous hamiltonian J (t : Complex) *
        asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) t := by
  let _ : NormedAlgebra Real (ContinuousSuperoperator H) :=
    NormedAlgebra.restrictScalars Real Complex (ContinuousSuperoperator H)
  change HasDerivAt
    (fun s : Real => NormedSpace.exp
      (s • asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)))
    (NormedSpace.exp (t • asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) *
      asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) t
  exact hasDerivAt_exp_smul_const
    (asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) t
end QEC.Semantics
