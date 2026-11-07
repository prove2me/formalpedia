-- Prove2me | solution 1 for QEC.Distillation.GeneratedUniversality.globalPhaseEquivalent_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:08:43.042617+00:00
-- url     : https://prove2.me/submissions/10c4466e-01c6-441b-80cc-9371efed6084

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
    GlobalPhaseEquivalent U⁻¹ V⁻¹ := by
  rcases h with ⟨scalar, hnorm, hmatrix⟩
  refine ⟨star scalar, ?_, ?_⟩
  · simpa using hnorm
  · change (↑(V⁻¹) : Matrix n n Complex) = star scalar • (↑(U⁻¹) : Matrix n n Complex)
    simp only [Matrix.UnitaryGroup.inv_val]
    rw [hmatrix, star_smul]
end QEC.Distillation.GeneratedUniversality
