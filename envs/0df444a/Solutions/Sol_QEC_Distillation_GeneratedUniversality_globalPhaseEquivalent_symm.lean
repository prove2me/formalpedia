-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.globalPhaseEquivalent_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:08:34.188199+00:00
-- url     : https://prove2.me/submissions/faf101ba-d8e2-44dc-82a2-8f6801d40e29

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
    {U V : UnitaryGate n} (h : GlobalPhaseEquivalent U V) :
    GlobalPhaseEquivalent V U := by
  rcases h with ⟨scalar, hnorm, hmatrix⟩
  have hnonzero : scalar ≠ 0 := by
    intro hzero
    simp [hzero] at hnorm
  refine ⟨scalar⁻¹, ?_, ?_⟩
  · rw [norm_inv, hnorm]
    norm_num
  · rw [hmatrix, smul_smul, inv_mul_cancel₀ hnonzero, one_smul]
end QEC.Distillation.GeneratedUniversality
