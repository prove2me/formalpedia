-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.approximatesModuloPhase_congr_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:09:18.307396+00:00
-- url     : https://prove2.me/submissions/a4b12683-1dc1-49ca-adc2-acc3c94222e4

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
universe u
open QEC
open QEC.Distillation
open QEC.Distillation.GeneratedUniversality
open Semantics
open scoped Matrix.Norms.Elementwise
namespace QEC.Distillation.GeneratedUniversality
theorem _root_.solution {n : Type u} [Fintype n] [DecidableEq n]
    {generators : Set (UnitaryGate n)} {target target' : UnitaryGate n} {precision : Real}
    (htarget : GlobalPhaseEquivalent target target')
    (happrox : ApproximatesModuloPhase generators target precision) :
    ApproximatesModuloPhase generators target' precision := by
  rcases htarget with ⟨phase, hnorm, hmatrix⟩
  rcases happrox with ⟨candidate, hcandidate, scalar, hscalar, hbound⟩
  have hnonzero : phase ≠ 0 := by
    intro hzero
    simp [hzero] at hnorm
  refine ⟨candidate, hcandidate, scalar * phase⁻¹, ?_, ?_⟩
  · rw [norm_mul, hscalar, norm_inv, hnorm]
    norm_num
  · rw [hmatrix, smul_smul]
    have hphase_cancel : scalar * phase⁻¹ * phase = scalar := by
      calc
        scalar * phase⁻¹ * phase = scalar * (phase⁻¹ * phase) := by ring
        _ = scalar := by rw [inv_mul_cancel₀ hnonzero, mul_one]
    rw [hphase_cancel]
    exact hbound
end QEC.Distillation.GeneratedUniversality
