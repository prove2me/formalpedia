-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.projectionSquaredOverlap_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:59:54.929508+00:00
-- url     : https://prove2.me/submissions/d2838774-260e-4adb-92c4-b4dba7b2cbfb

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_density_exists_rankOne_ensemble
import Theorems.Thm_QEC_Distillation_OneQubitMagic_rankOne_ensemble_norm_sq_sum_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_trace_mul_rankOne
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution
    (P : Operator QubitSpace) (rho : DensityOperator QubitSpace)
    (hP : P.IsSymmetricProjection) :
    projectionSquaredOverlap P rho ∈ Set.Icc 0 1 := by
  rcases density_exists_rankOne_ensemble rho with ⟨m, u, hensemble⟩
  have hnorm := rankOne_ensemble_norm_sq_sum_one rho u hensemble
  have hoverlap :
      projectionSquaredOverlap P rho =
        ∑ i, (inner Complex (u i) (P (u i))).re := by
    unfold projectionSquaredOverlap
    rw [hensemble, Finset.mul_sum]
    simp [map_sum, trace_mul_rankOne]
  have hOne : (1 : Operator QubitSpace).IsSymmetricProjection := by
    constructor
    · exact one_mul _
    · intro x y
      simp
  have hComplement : LinearMap.IsPositive (1 - P) :=
    (hP.sub_of_range_le_range hOne (by
      intro y _
      exact ⟨y, by simp⟩)).isPositive
  rw [hoverlap]
  constructor
  · exact Finset.sum_nonneg fun i _ =>
      hP.isPositive.re_inner_nonneg_right (u i)
  · calc
      (∑ i, (inner Complex (u i) (P (u i))).re) ≤
          ∑ i, ‖u i‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hnonneg := hComplement.re_inner_nonneg_right (u i)
        simpa [sub_apply, inner_sub_right, inner_self_eq_norm_sq_to_K,
          map_sub, pow_two] using hnonneg
      _ = 1 := hnorm
end QEC.Distillation.OneQubitMagic
