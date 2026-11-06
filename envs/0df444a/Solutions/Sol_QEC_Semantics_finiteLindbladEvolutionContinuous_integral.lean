-- Prove2me | solution 1 for QEC.Semantics.finiteLindbladEvolutionContinuous_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:06:04.738085+00:00
-- url     : https://prove2.me/submissions/b97159ec-5885-4cf0-912a-d505d435dd86

import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Theorems.Thm_QEC_Semantics_CompletelyPositive_intervalIntegral
import Theorems.Thm_QEC_Semantics_hasDerivAt_finiteLindbladEvolutionReal

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
    (hamiltonian : Operator H) (J : ι → Operator H)
    (t : Real) :
    (∫ s in (0 : Real)..t,
      finiteLindbladEvolutionContinuous hamiltonian J (s : Complex) *
        asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) =
      finiteLindbladEvolutionContinuous hamiltonian J (t : Complex) - 1 := by
  have hderiv : ∀ s : Real, HasDerivAt
      (fun r : Real => finiteLindbladEvolutionContinuous hamiltonian J (r : Complex))
      (finiteLindbladEvolutionContinuous hamiltonian J (s : Complex) *
        asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) s :=
    fun s => hasDerivAt_finiteLindbladEvolutionReal hamiltonian J s
  have hint : IntervalIntegrable
      (fun s : Real => finiteLindbladEvolutionContinuous hamiltonian J (s : Complex) *
        asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J))
      MeasureTheory.volume 0 t := by
    apply Continuous.intervalIntegrable
    exact continuous_iff_continuousAt.mpr fun s =>
      (hasDerivAt_finiteLindbladEvolutionReal hamiltonian J s).continuousAt.mul
        continuousAt_const
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _hs => hderiv s) hint
  have hzeroCast : finiteLindbladEvolutionContinuous hamiltonian J
      ((0 : Real) : Complex) = 1 := by
    change finiteLindbladEvolutionContinuous hamiltonian J (0 : Complex) = 1
    exact finiteLindbladEvolutionContinuous_zero hamiltonian J
  rw [hzeroCast] at hfund
  exact hfund
end QEC.Semantics
