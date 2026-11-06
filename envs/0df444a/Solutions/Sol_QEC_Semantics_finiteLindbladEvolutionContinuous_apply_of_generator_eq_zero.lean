-- Prove2me | solution 1 for QEC.Semantics.finiteLindbladEvolutionContinuous_apply_of_generator_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:05:00.219599+00:00
-- url     : https://prove2.me/submissions/6a226e0c-6ea9-4072-8d8a-cdb9da5ede44

import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Theorems.Thm_QEC_Semantics_hasDerivAt_finiteLindbladEvolutionContinuous
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg



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
    (hstationary : finiteLindbladGenerator hamiltonian J A = 0) (z : Complex) :
    finiteLindbladEvolutionContinuous hamiltonian J z
      (LinearMap.toContinuousLinearMap A) = LinearMap.toContinuousLinearMap A := by
  let E := finiteLindbladEvolutionContinuous hamiltonian J
  let G := asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)
  let Ac := LinearMap.toContinuousLinearMap A
  have hG : G Ac = 0 := by
    change LinearMap.toContinuousLinearMap
      (finiteLindbladGenerator hamiltonian J A) = 0
    rw [hstationary]
    rfl
  have hderiv : ∀ w : Complex, HasDerivAt (fun z => E z Ac) 0 w := by
    intro w
    have hE : HasDerivAt E (E w * G) w :=
      hasDerivAt_finiteLindbladEvolutionContinuous hamiltonian J w
    have hEA := hE.clm_apply (hasDerivAt_const w Ac)
    have hzero : (E w * G) Ac = 0 := by
      change E w (G Ac) = 0
      rw [hG]
      exact map_zero (E w)
    simp only [map_zero, add_zero, hzero] at hEA
    exact hEA
  have hdiff : Differentiable Complex (fun w => E w Ac) :=
    fun w => (hderiv w).differentiableAt
  have hderiv_zero : ∀ w, deriv (fun z => E z Ac) w = 0 :=
    fun w => (hderiv w).deriv
  have hconst := is_const_of_deriv_eq_zero hdiff hderiv_zero z 0
  simpa [E, Ac] using hconst
end QEC.Semantics
