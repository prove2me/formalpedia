-- Prove2me | solution 1 for QEC.Semantics.finiteLindbladEvolutionLinearMap_apply_of_generator_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:03:24.856809+00:00
-- url     : https://prove2.me/submissions/fb0e3773-ceb9-49dd-8f58-8418cba513ce

import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionContinuous_apply_of_generator_eq_zero

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
    (hamiltonian : Operator H) (J : ι → Operator H) (A : Operator H)
    (hstationary : finiteLindbladGenerator hamiltonian J A = 0) (t : Real) :
    finiteLindbladEvolutionLinearMap hamiltonian J t A = A := by
  change LinearMap.toContinuousLinearMap.symm
    (finiteLindbladEvolutionContinuous hamiltonian J (t : Complex)
      (LinearMap.toContinuousLinearMap A)) = A
  rw [finiteLindbladEvolutionContinuous_apply_of_generator_eq_zero
    hamiltonian J A hstationary]
  rfl
end QEC.Semantics
